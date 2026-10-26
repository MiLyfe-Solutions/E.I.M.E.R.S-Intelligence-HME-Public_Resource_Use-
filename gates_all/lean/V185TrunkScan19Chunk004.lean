import V185TrunkScan19Chunk003

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_40033 : List Nat := [1, 2, 3, 1, 1, 2, 5, 4]
def baseStart_40033 : Nat := 118140960795 + 40033 * 2 ^ 59
def prefixEnd_40033 : Nat := 4983230072969 + 3 ^ 40 * 40033 * 2
def baseEnd_40033 : Nat := 12181434691287172979791

theorem tailTrace_40033 : CollatzResearch.WordTrace tailWord_40033 prefixEnd_40033 12181434691287172979791 := by
  unfold tailWord_40033
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460123463974752937180753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 973415642649835291453835 1460123463974752937180753)
  ·
    refine ⟨1095092597981064702885565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1460123463974752937180753 1095092597981064702885565)
    ·
      refine ⟨410659724242899263582087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1095092597981064702885565 410659724242899263582087)
      ·
        refine ⟨615989586364348895373131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410659724242899263582087 615989586364348895373131)
        ·
          refine ⟨923984379546523343059697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615989586364348895373131 923984379546523343059697)
          ·
            refine ⟨692988284659892507294773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 923984379546523343059697 692988284659892507294773)
            ·
              refine ⟨64967651686864922558885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 692988284659892507294773 64967651686864922558885)
              ·
                refine ⟨12181434691287172979791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64967651686864922558885 12181434691287172979791)
                ·
                  rfl

theorem cell19_40033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_40033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40033 prefixEnd_40033 := by exact prefixLift 40033
  have htrace : WordTrace (prefixWord ++ tailWord_40033) baseStart_40033 baseEnd_40033 := by
    simpa [prefixWord, tailWord_40033, baseEnd_40033] using wordTrace_append hprefix tailTrace_40033
  have hstable : (prefixWord ++ tailWord_40033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40033).length < 2 ^ (prefixWord ++ tailWord_40033).sum := by decide
  have hdescent : baseEnd_40033 < baseStart_40033 := by decide
  rcases family_descends (prefixWord ++ tailWord_40033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40050 : List Nat := [3, 2, 1, 2, 2, 1, 5, 3]
def baseStart_40050 : Nat := 118140960795 + 40050 * 2 ^ 59
def prefixEnd_40050 : Nat := 4983230072969 + 3 ^ 40 * 40050 * 2
def baseEnd_40050 : Nat := 12186607533436170601967

theorem tailTrace_40050 : CollatzResearch.WordTrace tailWord_40050 prefixEnd_40050 12186607533436170601967 := by
  unfold tailWord_40050
  simp only [CollatzResearch.WordTrace]
  refine ⟨365185876228291210137401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 973829003275443227033069 365185876228291210137401)
  ·
    refine ⟨273889407171218407603051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 365185876228291210137401 273889407171218407603051)
    ·
      refine ⟨410834110756827611404577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273889407171218407603051 410834110756827611404577)
      ·
        refine ⟨308125583067620708553433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410834110756827611404577 308125583067620708553433)
        ·
          refine ⟨231094187300715531415075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308125583067620708553433 231094187300715531415075)
          ·
            refine ⟨346641280951073297122613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231094187300715531415075 346641280951073297122613)
            ·
              refine ⟨32497620089163121605245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 346641280951073297122613 32497620089163121605245)
              ·
                refine ⟨12186607533436170601967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32497620089163121605245 12186607533436170601967)
                ·
                  rfl

theorem cell19_40050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_40050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40050 prefixEnd_40050 := by exact prefixLift 40050
  have htrace : WordTrace (prefixWord ++ tailWord_40050) baseStart_40050 baseEnd_40050 := by
    simpa [prefixWord, tailWord_40050, baseEnd_40050] using wordTrace_append hprefix tailTrace_40050
  have hstable : (prefixWord ++ tailWord_40050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40050).length < 2 ^ (prefixWord ++ tailWord_40050).sum := by decide
  have hdescent : baseEnd_40050 < baseStart_40050 := by decide
  rcases family_descends (prefixWord ++ tailWord_40050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40126 : List Nat := [4, 2, 1, 1, 3, 3, 5]
def baseStart_40126 : Nat := 118140960795 + 40126 * 2 ^ 59
def prefixEnd_40126 : Nat := 4983230072969 + 3 ^ 40 * 40126 * 2
def baseEnd_40126 : Nat := 4069911060230170970957

theorem tailTrace_40126 : CollatzResearch.WordTrace tailWord_40126 prefixEnd_40126 4069911060230170970957 := by
  unfold tailWord_40126
  simp only [CollatzResearch.WordTrace]
  refine ⟨182939431579728727539529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 975676968425219880210821 182939431579728727539529)
  ·
    refine ⟨137204573684796545654647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182939431579728727539529 137204573684796545654647)
    ·
      refine ⟨205806860527194818481971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137204573684796545654647 205806860527194818481971)
      ·
        refine ⟨308710290790792227722957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205806860527194818481971 308710290790792227722957)
        ·
          refine ⟨115766359046547085396109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308710290790792227722957 115766359046547085396109)
          ·
            refine ⟨43412384642455157023541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115766359046547085396109 43412384642455157023541)
            ·
              refine ⟨4069911060230170970957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43412384642455157023541 4069911060230170970957)
              ·
                rfl

theorem cell19_40126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_40126 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40126 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40126 prefixEnd_40126 := by exact prefixLift 40126
  have htrace : WordTrace (prefixWord ++ tailWord_40126) baseStart_40126 baseEnd_40126 := by
    simpa [prefixWord, tailWord_40126, baseEnd_40126] using wordTrace_append hprefix tailTrace_40126
  have hstable : (prefixWord ++ tailWord_40126).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40126).length < 2 ^ (prefixWord ++ tailWord_40126).sum := by decide
  have hdescent : baseEnd_40126 < baseStart_40126 := by decide
  rcases family_descends (prefixWord ++ tailWord_40126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40141 : List Nat := [1, 6, 2, 2, 1, 1, 2, 4]
def baseStart_40141 : Nat := 118140960795 + 40141 * 2 ^ 59
def prefixEnd_40141 : Nat := 4983230072969 + 3 ^ 40 * 40141 * 2
def baseEnd_40141 : Nat := 12214297453174922579497

theorem tailTrace_40141 : CollatzResearch.WordTrace tailWord_40141 prefixEnd_40141 12214297453174922579497 := by
  unfold tailWord_40141
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464062547583487382112277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 976041698388991588074851 1464062547583487382112277)
  ·
    refine ⟨68627931917975971036513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1464062547583487382112277 68627931917975971036513)
    ·
      refine ⟨51470948938481978277385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68627931917975971036513 51470948938481978277385)
      ·
        refine ⟨38603211703861483708039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51470948938481978277385 38603211703861483708039)
        ·
          refine ⟨57904817555792225562059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38603211703861483708039 57904817555792225562059)
          ·
            refine ⟨86857226333688338343089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57904817555792225562059 86857226333688338343089)
            ·
              refine ⟨65142919750266253757317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86857226333688338343089 65142919750266253757317)
              ·
                refine ⟨12214297453174922579497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65142919750266253757317 12214297453174922579497)
                ·
                  rfl

theorem cell19_40141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_40141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40141 prefixEnd_40141 := by exact prefixLift 40141
  have htrace : WordTrace (prefixWord ++ tailWord_40141) baseStart_40141 baseEnd_40141 := by
    simpa [prefixWord, tailWord_40141, baseEnd_40141] using wordTrace_append hprefix tailTrace_40141
  have hstable : (prefixWord ++ tailWord_40141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40141).length < 2 ^ (prefixWord ++ tailWord_40141).sum := by decide
  have hdescent : baseEnd_40141 < baseStart_40141 := by decide
  rcases family_descends (prefixWord ++ tailWord_40141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40200 : List Nat := [2, 1, 3, 2, 5, 1, 1, 4]
def baseStart_40200 : Nat := 118140960795 + 40200 * 2 ^ 59
def prefixEnd_40200 : Nat := 4983230072969 + 3 ^ 40 * 40200 * 2
def baseEnd_40200 : Nat := 12232250258280267268225

theorem tailTrace_40200 : CollatzResearch.WordTrace tailWord_40200 prefixEnd_40200 12232250258280267268225 := by
  unfold tailWord_40200
  simp only [CollatzResearch.WordTrace]
  refine ⟨733107227184870229255027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 977476302913160305673369 733107227184870229255027)
  ·
    refine ⟨1099660840777305343882541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 733107227184870229255027 1099660840777305343882541)
    ·
      refine ⟨412372815291489503955953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1099660840777305343882541 412372815291489503955953)
      ·
        refine ⟨309279611468617127966965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412372815291489503955953 309279611468617127966965)
        ·
          refine ⟨28994963575182855746903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 309279611468617127966965 28994963575182855746903)
          ·
            refine ⟨43492445362774283620355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28994963575182855746903 43492445362774283620355)
            ·
              refine ⟨65238668044161425430533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43492445362774283620355 65238668044161425430533)
              ·
                refine ⟨12232250258280267268225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65238668044161425430533 12232250258280267268225)
                ·
                  rfl

theorem cell19_40200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_40200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40200 prefixEnd_40200 := by exact prefixLift 40200
  have htrace : WordTrace (prefixWord ++ tailWord_40200) baseStart_40200 baseEnd_40200 := by
    simpa [prefixWord, tailWord_40200, baseEnd_40200] using wordTrace_append hprefix tailTrace_40200
  have hstable : (prefixWord ++ tailWord_40200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40200).length < 2 ^ (prefixWord ++ tailWord_40200).sum := by decide
  have hdescent : baseEnd_40200 < baseStart_40200 := by decide
  rcases family_descends (prefixWord ++ tailWord_40200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40204 : List Nat := [2, 2, 1, 2, 2, 3, 3, 4]
def baseStart_40204 : Nat := 118140960795 + 40204 * 2 ^ 59
def prefixEnd_40204 : Nat := 4983230072969 + 3 ^ 40 * 40204 * 2
def baseEnd_40204 : Nat := 12233467397609443179325

theorem tailTrace_40204 : CollatzResearch.WordTrace tailWord_40204 prefixEnd_40204 12233467397609443179325 := by
  unfold tailWord_40204
  simp only [CollatzResearch.WordTrace]
  refine ⟨733180173177624570827833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 977573564236832761103777 733180173177624570827833)
  ·
    refine ⟨549885129883218428120875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 733180173177624570827833 549885129883218428120875)
    ·
      refine ⟨824827694824827642181313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549885129883218428120875 824827694824827642181313)
      ·
        refine ⟨618620771118620731635985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824827694824827642181313 618620771118620731635985)
        ·
          refine ⟨463965578338965548726989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618620771118620731635985 463965578338965548726989)
          ·
            refine ⟨173987091877112080772621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 463965578338965548726989 173987091877112080772621)
            ·
              refine ⟨65245159453917030289733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173987091877112080772621 65245159453917030289733)
              ·
                refine ⟨12233467397609443179325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65245159453917030289733 12233467397609443179325)
                ·
                  rfl

theorem cell19_40204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_40204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40204 prefixEnd_40204 := by exact prefixLift 40204
  have htrace : WordTrace (prefixWord ++ tailWord_40204) baseStart_40204 baseEnd_40204 := by
    simpa [prefixWord, tailWord_40204, baseEnd_40204] using wordTrace_append hprefix tailTrace_40204
  have hstable : (prefixWord ++ tailWord_40204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40204).length < 2 ^ (prefixWord ++ tailWord_40204).sum := by decide
  have hdescent : baseEnd_40204 < baseStart_40204 := by decide
  rcases family_descends (prefixWord ++ tailWord_40204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40242 : List Nat := [3, 2, 1, 1, 4, 2, 6]
def baseStart_40242 : Nat := 118140960795 + 40242 * 2 ^ 59
def prefixEnd_40242 : Nat := 4983230072969 + 3 ^ 40 * 40242 * 2
def baseEnd_40242 : Nat := 4081676740412204778259

theorem tailTrace_40242 : CollatzResearch.WordTrace tailWord_40242 prefixEnd_40242 4081676740412204778259 := by
  unfold tailWord_40242
  simp only [CollatzResearch.WordTrace]
  refine ⟨366936580054395407884745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 978497546811721087692653 366936580054395407884745)
  ·
    refine ⟨275202435040796555913559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 366936580054395407884745 275202435040796555913559)
    ·
      refine ⟨412803652561194833870339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275202435040796555913559 412803652561194833870339)
      ·
        refine ⟨619205478841792250805509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412803652561194833870339 619205478841792250805509)
        ·
          refine ⟨116101027282836047026033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 619205478841792250805509 116101027282836047026033)
          ·
            refine ⟨87075770462127035269525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116101027282836047026033 87075770462127035269525)
            ·
              refine ⟨4081676740412204778259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87075770462127035269525 4081676740412204778259)
              ·
                rfl

theorem cell19_40242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_40242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40242 prefixEnd_40242 := by exact prefixLift 40242
  have htrace : WordTrace (prefixWord ++ tailWord_40242) baseStart_40242 baseEnd_40242 := by
    simpa [prefixWord, tailWord_40242, baseEnd_40242] using wordTrace_append hprefix tailTrace_40242
  have hstable : (prefixWord ++ tailWord_40242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40242).length < 2 ^ (prefixWord ++ tailWord_40242).sum := by decide
  have hdescent : baseEnd_40242 < baseStart_40242 := by decide
  rcases family_descends (prefixWord ++ tailWord_40242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40373 : List Nat := [1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_40373 : Nat := 118140960795 + 40373 * 2 ^ 59
def prefixEnd_40373 : Nat := 4983230072969 + 3 ^ 40 * 40373 * 2
def baseEnd_40373 : Nat := 12284891534267125423309

theorem tailTrace_40373 : CollatzResearch.WordTrace tailWord_40373 prefixEnd_40373 12284891534267125423309 := by
  unfold tailWord_40373
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472524282742991004557773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 981682855161994003038515 1472524282742991004557773)
  ·
    refine ⟨552196606028621626709165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1472524282742991004557773 552196606028621626709165)
    ·
      refine ⟨207073727260733110015937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 552196606028621626709165 207073727260733110015937)
      ·
        refine ⟨155305295445549832511953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207073727260733110015937 155305295445549832511953)
        ·
          refine ⟨116478971584162374383965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155305295445549832511953 116478971584162374383965)
          ·
            refine ⟨43679614344060890393987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116478971584162374383965 43679614344060890393987)
            ·
              refine ⟨65519421516091335590981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43679614344060890393987 65519421516091335590981)
              ·
                refine ⟨12284891534267125423309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65519421516091335590981 12284891534267125423309)
                ·
                  rfl

theorem cell19_40373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_40373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40373 prefixEnd_40373 := by exact prefixLift 40373
  have htrace : WordTrace (prefixWord ++ tailWord_40373) baseStart_40373 baseEnd_40373 := by
    simpa [prefixWord, tailWord_40373, baseEnd_40373] using wordTrace_append hprefix tailTrace_40373
  have hstable : (prefixWord ++ tailWord_40373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40373).length < 2 ^ (prefixWord ++ tailWord_40373).sum := by decide
  have hdescent : baseEnd_40373 < baseStart_40373 := by decide
  rcases family_descends (prefixWord ++ tailWord_40373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40413 : List Nat := [1, 4, 3, 1, 1, 3, 6]
def baseStart_40413 : Nat := 118140960795 + 40413 * 2 ^ 59
def prefixEnd_40413 : Nat := 4983230072969 + 3 ^ 40 * 40413 * 2
def baseEnd_40413 : Nat := 4099020975852961511437

theorem tailTrace_40413 : CollatzResearch.WordTrace tailWord_40413 prefixEnd_40413 4099020975852961511437 := by
  unfold tailWord_40413
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473983202598077836013893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 982655468398718557342595 1473983202598077836013893)
  ·
    refine ⟨276371850487139594252605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1473983202598077836013893 276371850487139594252605)
    ·
      refine ⟨103639443932677347844727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276371850487139594252605 103639443932677347844727)
      ·
        refine ⟨155459165899016021767091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103639443932677347844727 155459165899016021767091)
        ·
          refine ⟨233188748848524032650637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155459165899016021767091 233188748848524032650637)
          ·
            refine ⟨87445780818196512243989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233188748848524032650637 87445780818196512243989)
            ·
              refine ⟨4099020975852961511437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87445780818196512243989 4099020975852961511437)
              ·
                rfl

theorem cell19_40413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_40413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40413 prefixEnd_40413 := by exact prefixLift 40413
  have htrace : WordTrace (prefixWord ++ tailWord_40413) baseStart_40413 baseEnd_40413 := by
    simpa [prefixWord, tailWord_40413, baseEnd_40413] using wordTrace_append hprefix tailTrace_40413
  have hstable : (prefixWord ++ tailWord_40413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40413).length < 2 ^ (prefixWord ++ tailWord_40413).sum := by decide
  have hdescent : baseEnd_40413 < baseStart_40413 := by decide
  rcases family_descends (prefixWord ++ tailWord_40413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40415 : List Nat := [1, 1, 2, 3, 3, 1, 8]
def baseStart_40415 : Nat := 118140960795 + 40415 * 2 ^ 59
def prefixEnd_40415 : Nat := 4983230072969 + 3 ^ 40 * 40415 * 2
def baseEnd_40415 : Nat := 4099223832407824163287

theorem tailTrace_40415 : CollatzResearch.WordTrace tailWord_40415 prefixEnd_40415 4099223832407824163287 := by
  unfold tailWord_40415
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474056148590832177586699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 982704099060554785057799 1474056148590832177586699)
  ·
    refine ⟨2211084222886248266380049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1474056148590832177586699 2211084222886248266380049)
    ·
      refine ⟨1658313167164686199785037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2211084222886248266380049 1658313167164686199785037)
      ·
        refine ⟨621867437686757324919389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1658313167164686199785037 621867437686757324919389)
        ·
          refine ⟨233200289132533996844771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 621867437686757324919389 233200289132533996844771)
          ·
            refine ⟨349800433698800995267157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233200289132533996844771 349800433698800995267157)
            ·
              refine ⟨4099223832407824163287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 349800433698800995267157 4099223832407824163287)
              ·
                rfl

theorem cell19_40415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_40415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40415 prefixEnd_40415 := by exact prefixLift 40415
  have htrace : WordTrace (prefixWord ++ tailWord_40415) baseStart_40415 baseEnd_40415 := by
    simpa [prefixWord, tailWord_40415, baseEnd_40415] using wordTrace_append hprefix tailTrace_40415
  have hstable : (prefixWord ++ tailWord_40415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40415).length < 2 ^ (prefixWord ++ tailWord_40415).sum := by decide
  have hdescent : baseEnd_40415 < baseStart_40415 := by decide
  rcases family_descends (prefixWord ++ tailWord_40415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40525 : List Nat := [1, 6, 1, 1, 4, 6]
def baseStart_40525 : Nat := 118140960795 + 40525 * 2 ^ 59
def prefixEnd_40525 : Nat := 4983230072969 + 3 ^ 40 * 40525 * 2
def baseEnd_40525 : Nat := 1370126980975090005013

theorem tailTrace_40525 : CollatzResearch.WordTrace tailWord_40525 prefixEnd_40525 1370126980975090005013 := by
  unfold tailWord_40525
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478068178192320964091029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 985378785461547309394019 1478068178192320964091029)
  ·
    refine ⟨69284445852765045191767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1478068178192320964091029 69284445852765045191767)
    ·
      refine ⟨103926668779147567787651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69284445852765045191767 103926668779147567787651)
      ·
        refine ⟨155890003168721351681477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103926668779147567787651 155890003168721351681477)
        ·
          refine ⟨29229375594135253440277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155890003168721351681477 29229375594135253440277)
          ·
            refine ⟨1370126980975090005013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29229375594135253440277 1370126980975090005013)
            ·
              rfl

theorem cell19_40525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 6].length) (baseStart_40525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40525 prefixEnd_40525 := by exact prefixLift 40525
  have htrace : WordTrace (prefixWord ++ tailWord_40525) baseStart_40525 baseEnd_40525 := by
    simpa [prefixWord, tailWord_40525, baseEnd_40525] using wordTrace_append hprefix tailTrace_40525
  have hstable : (prefixWord ++ tailWord_40525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40525).length < 2 ^ (prefixWord ++ tailWord_40525).sum := by decide
  have hdescent : baseEnd_40525 < baseStart_40525 := by decide
  rcases family_descends (prefixWord ++ tailWord_40525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40605 : List Nat := [1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_40605 : Nat := 118140960795 + 40605 * 2 ^ 59
def prefixEnd_40605 : Nat := 4983230072969 + 3 ^ 40 * 40605 * 2
def baseEnd_40605 : Nat := 12355485615359328267121

theorem tailTrace_40605 : CollatzResearch.WordTrace tailWord_40605 prefixEnd_40605 12355485615359328267121 := by
  unfold tailWord_40605
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480986017902494627003269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 987324011934996418002179 1480986017902494627003269)
  ·
    refine ⟨277684878356717742563113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1480986017902494627003269 277684878356717742563113)
    ·
      refine ⟨208263658767538306922335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 277684878356717742563113 208263658767538306922335)
      ·
        refine ⟨312395488151307460383503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208263658767538306922335 312395488151307460383503)
        ·
          refine ⟨468593232226961190575255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312395488151307460383503 468593232226961190575255)
          ·
            refine ⟨702889848340441785862883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468593232226961190575255 702889848340441785862883)
            ·
              refine ⟨1054334772510662678794325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702889848340441785862883 1054334772510662678794325)
              ·
                refine ⟨12355485615359328267121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1054334772510662678794325 12355485615359328267121)
                ·
                  rfl

theorem cell19_40605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_40605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40605 prefixEnd_40605 := by exact prefixLift 40605
  have htrace : WordTrace (prefixWord ++ tailWord_40605) baseStart_40605 baseEnd_40605 := by
    simpa [prefixWord, tailWord_40605, baseEnd_40605] using wordTrace_append hprefix tailTrace_40605
  have hstable : (prefixWord ++ tailWord_40605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40605).length < 2 ^ (prefixWord ++ tailWord_40605).sum := by decide
  have hdescent : baseEnd_40605 < baseStart_40605 := by decide
  rcases family_descends (prefixWord ++ tailWord_40605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40660 : List Nat := [2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_40660 : Nat := 118140960795 + 40660 * 2 ^ 59
def prefixEnd_40660 : Nat := 4983230072969 + 3 ^ 40 * 40660 * 2
def baseEnd_40660 : Nat := 12372221281135497044749

theorem tailTrace_40660 : CollatzResearch.WordTrace tailWord_40660 prefixEnd_40660 12372221281135497044749 := by
  unfold tailWord_40660
  simp only [CollatzResearch.WordTrace]
  refine ⟨741496016351619510127717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 988661355135492680170289 741496016351619510127717)
  ·
    refine ⟨139030503065928658148947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 741496016351619510127717 139030503065928658148947)
    ·
      refine ⟨208545754598892987223421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139030503065928658148947 208545754598892987223421)
      ·
        refine ⟨78204657974584870208783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208545754598892987223421 78204657974584870208783)
        ·
          refine ⟨117306986961877305313175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78204657974584870208783 117306986961877305313175)
          ·
            refine ⟨175960480442815957969763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117306986961877305313175 175960480442815957969763)
            ·
              refine ⟨263940720664223936954645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175960480442815957969763 263940720664223936954645)
              ·
                refine ⟨12372221281135497044749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 263940720664223936954645 12372221281135497044749)
                ·
                  rfl

theorem cell19_40660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_40660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40660 prefixEnd_40660 := by exact prefixLift 40660
  have htrace : WordTrace (prefixWord ++ tailWord_40660) baseStart_40660 baseEnd_40660 := by
    simpa [prefixWord, tailWord_40660, baseEnd_40660] using wordTrace_append hprefix tailTrace_40660
  have hstable : (prefixWord ++ tailWord_40660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40660).length < 2 ^ (prefixWord ++ tailWord_40660).sum := by decide
  have hdescent : baseEnd_40660 < baseStart_40660 := by decide
  rcases family_descends (prefixWord ++ tailWord_40660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40736 : List Nat := [2, 1, 1, 5, 1, 1, 5, 3]
def baseStart_40736 : Nat := 118140960795 + 40736 * 2 ^ 59
def prefixEnd_40736 : Nat := 4983230072969 + 3 ^ 40 * 40736 * 2
def baseEnd_40736 : Nat := 12395346928389839355653

theorem tailTrace_40736 : CollatzResearch.WordTrace tailWord_40736 prefixEnd_40736 12395346928389839355653 := by
  unfold tailWord_40736
  simp only [CollatzResearch.WordTrace]
  refine ⟨742881990213952000011031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 990509320285269333348041 742881990213952000011031)
  ·
    refine ⟨1114322985320928000016547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 742881990213952000011031 1114322985320928000016547)
    ·
      refine ⟨1671484477981392000024821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114322985320928000016547 1671484477981392000024821)
      ·
        refine ⟨156701669810755500002327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1671484477981392000024821 156701669810755500002327)
        ·
          refine ⟨235052504716133250003491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156701669810755500002327 235052504716133250003491)
          ·
            refine ⟨352578757074199875005237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235052504716133250003491 352578757074199875005237)
            ·
              refine ⟨33054258475706238281741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 352578757074199875005237 33054258475706238281741)
              ·
                refine ⟨12395346928389839355653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33054258475706238281741 12395346928389839355653)
                ·
                  rfl

theorem cell19_40736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_40736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40736 prefixEnd_40736 := by exact prefixLift 40736
  have htrace : WordTrace (prefixWord ++ tailWord_40736) baseStart_40736 baseEnd_40736 := by
    simpa [prefixWord, tailWord_40736, baseEnd_40736] using wordTrace_append hprefix tailTrace_40736
  have hstable : (prefixWord ++ tailWord_40736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40736).length < 2 ^ (prefixWord ++ tailWord_40736).sum := by decide
  have hdescent : baseEnd_40736 < baseStart_40736 := by decide
  rcases family_descends (prefixWord ++ tailWord_40736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40791 : List Nat := [1, 1, 3, 2, 5, 2, 2, 3]
def baseStart_40791 : Nat := 118140960795 + 40791 * 2 ^ 59
def prefixEnd_40791 : Nat := 4983230072969 + 3 ^ 40 * 40791 * 2
def baseEnd_40791 : Nat := 12412082594166008133281

theorem tailTrace_40791 : CollatzResearch.WordTrace tailWord_40791 prefixEnd_40791 12412082594166008133281 := by
  unfold tailWord_40791
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487769995228648393274227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 991846663485765595516151 1487769995228648393274227)
  ·
    refine ⟨2231654992842972589911341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1487769995228648393274227 2231654992842972589911341)
    ·
      refine ⟨836870622316114721216753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2231654992842972589911341 836870622316114721216753)
      ·
        refine ⟨627652966737086040912565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 836870622316114721216753 627652966737086040912565)
        ·
          refine ⟨58842465631601816335553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 627652966737086040912565 58842465631601816335553)
          ·
            refine ⟨44131849223701362251665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58842465631601816335553 44131849223701362251665)
            ·
              refine ⟨33098886917776021688749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44131849223701362251665 33098886917776021688749)
              ·
                refine ⟨12412082594166008133281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33098886917776021688749 12412082594166008133281)
                ·
                  rfl

theorem cell19_40791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_40791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40791 prefixEnd_40791 := by exact prefixLift 40791
  have htrace : WordTrace (prefixWord ++ tailWord_40791) baseStart_40791 baseEnd_40791 := by
    simpa [prefixWord, tailWord_40791, baseEnd_40791] using wordTrace_append hprefix tailTrace_40791
  have hstable : (prefixWord ++ tailWord_40791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40791).length < 2 ^ (prefixWord ++ tailWord_40791).sum := by decide
  have hdescent : baseEnd_40791 < baseStart_40791 := by decide
  rcases family_descends (prefixWord ++ tailWord_40791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40810 : List Nat := [3, 1, 3, 4, 1, 2, 5]
def baseStart_40810 : Nat := 118140960795 + 40810 * 2 ^ 59
def prefixEnd_40810 : Nat := 4983230072969 + 3 ^ 40 * 40810 * 2
def baseEnd_40810 : Nat := 4139288001993197903669

theorem tailTrace_40810 : CollatzResearch.WordTrace tailWord_40810 prefixEnd_40810 4139288001993197903669 := by
  unfold tailWord_40810
  simp only [CollatzResearch.WordTrace]
  refine ⟨372115745539953659553971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 992308654773209758810589 372115745539953659553971)
  ·
    refine ⟨558173618309930489330957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 372115745539953659553971 558173618309930489330957)
    ·
      refine ⟨209315106866223933499109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 558173618309930489330957 209315106866223933499109)
      ·
        refine ⟨39246582537416987531083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209315106866223933499109 39246582537416987531083)
        ·
          refine ⟨58869873806125481296625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39246582537416987531083 58869873806125481296625)
          ·
            refine ⟨44152405354594110972469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58869873806125481296625 44152405354594110972469)
            ·
              refine ⟨4139288001993197903669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44152405354594110972469 4139288001993197903669)
              ·
                rfl

theorem cell19_40810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_40810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40810 prefixEnd_40810 := by exact prefixLift 40810
  have htrace : WordTrace (prefixWord ++ tailWord_40810) baseStart_40810 baseEnd_40810 := by
    simpa [prefixWord, tailWord_40810, baseEnd_40810] using wordTrace_append hprefix tailTrace_40810
  have hstable : (prefixWord ++ tailWord_40810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40810).length < 2 ^ (prefixWord ++ tailWord_40810).sum := by decide
  have hdescent : baseEnd_40810 < baseStart_40810 := by decide
  rcases family_descends (prefixWord ++ tailWord_40810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40850 : List Nat := [3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_40850 : Nat := 118140960795 + 40850 * 2 ^ 59
def prefixEnd_40850 : Nat := 4983230072969 + 3 ^ 40 * 40850 * 2
def baseEnd_40850 : Nat := 12430035399271352822009

theorem tailTrace_40850 : CollatzResearch.WordTrace tailWord_40850 prefixEnd_40850 12430035399271352822009 := by
  unfold tailWord_40850
  simp only [CollatzResearch.WordTrace]
  refine ⟨372480475503725367418001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 993281268009934313114669 372480475503725367418001)
  ·
    refine ⟨279360356627794025563501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 372480475503725367418001 279360356627794025563501)
    ·
      refine ⟨104760133735422759586313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279360356627794025563501 104760133735422759586313)
      ·
        refine ⟨78570100301567069689735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104760133735422759586313 78570100301567069689735)
        ·
          refine ⟨117855150452350604534603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78570100301567069689735 117855150452350604534603)
          ·
            refine ⟨176782725678525906801905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117855150452350604534603 176782725678525906801905)
            ·
              refine ⟨132587044258894430101429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176782725678525906801905 132587044258894430101429)
              ·
                refine ⟨12430035399271352822009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132587044258894430101429 12430035399271352822009)
                ·
                  rfl

theorem cell19_40850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_40850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40850 prefixEnd_40850 := by exact prefixLift 40850
  have htrace : WordTrace (prefixWord ++ tailWord_40850) baseStart_40850 baseEnd_40850 := by
    simpa [prefixWord, tailWord_40850, baseEnd_40850] using wordTrace_append hprefix tailTrace_40850
  have hstable : (prefixWord ++ tailWord_40850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40850).length < 2 ^ (prefixWord ++ tailWord_40850).sum := by decide
  have hdescent : baseEnd_40850 < baseStart_40850 := by decide
  rcases family_descends (prefixWord ++ tailWord_40850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40871 : List Nat := [1, 1, 6, 1, 2, 8]
def baseStart_40871 : Nat := 118140960795 + 40871 * 2 ^ 59
def prefixEnd_40871 : Nat := 4983230072969 + 3 ^ 40 * 40871 * 2
def baseEnd_40871 : Nat := 1381825042305502928365

theorem tailTrace_40871 : CollatzResearch.WordTrace tailWord_40871 prefixEnd_40871 1381825042305502928365 := by
  unfold tailWord_40871
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490687834938822056186467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 993791889959214704124311 1490687834938822056186467)
  ·
    refine ⟨2236031752408233084279701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1490687834938822056186467 2236031752408233084279701)
    ·
      refine ⟨104813988394135925825611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2236031752408233084279701 104813988394135925825611)
      ·
        refine ⟨157220982591203888738417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104813988394135925825611 157220982591203888738417)
        ·
          refine ⟨117915736943402916553813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157220982591203888738417 117915736943402916553813)
          ·
            refine ⟨1381825042305502928365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 117915736943402916553813 1381825042305502928365)
            ·
              rfl

theorem cell19_40871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 8].length) (baseStart_40871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40871 prefixEnd_40871 := by exact prefixLift 40871
  have htrace : WordTrace (prefixWord ++ tailWord_40871) baseStart_40871 baseEnd_40871 := by
    simpa [prefixWord, tailWord_40871, baseEnd_40871] using wordTrace_append hprefix tailTrace_40871
  have hstable : (prefixWord ++ tailWord_40871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40871).length < 2 ^ (prefixWord ++ tailWord_40871).sum := by decide
  have hdescent : baseEnd_40871 < baseStart_40871 := by decide
  rcases family_descends (prefixWord ++ tailWord_40871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40884 : List Nat := [2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_40884 : Nat := 118140960795 + 40884 * 2 ^ 59
def prefixEnd_40884 : Nat := 4983230072969 + 3 ^ 40 * 40884 * 2
def baseEnd_40884 : Nat := 12440381083569348066361

theorem tailTrace_40884 : CollatzResearch.WordTrace tailWord_40884 prefixEnd_40884 12440381083569348066361 := by
  unfold tailWord_40884
  simp only [CollatzResearch.WordTrace]
  refine ⟨745580991945862638204853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 994107989261150184273137 745580991945862638204853)
  ·
    refine ⟨69898217994924622331705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 745580991945862638204853 69898217994924622331705)
    ·
      refine ⟨52423663496193466748779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69898217994924622331705 52423663496193466748779)
      ·
        refine ⟨78635495244290200123169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52423663496193466748779 78635495244290200123169)
        ·
          refine ⟨58976621433217650092377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78635495244290200123169 58976621433217650092377)
          ·
            refine ⟨44232466074913237569283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58976621433217650092377 44232466074913237569283)
            ·
              refine ⟨66348699112369856353925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44232466074913237569283 66348699112369856353925)
              ·
                refine ⟨12440381083569348066361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66348699112369856353925 12440381083569348066361)
                ·
                  rfl

theorem cell19_40884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_40884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40884 prefixEnd_40884 := by exact prefixLift 40884
  have htrace : WordTrace (prefixWord ++ tailWord_40884) baseStart_40884 baseEnd_40884 := by
    simpa [prefixWord, tailWord_40884, baseEnd_40884] using wordTrace_append hprefix tailTrace_40884
  have hstable : (prefixWord ++ tailWord_40884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40884).length < 2 ^ (prefixWord ++ tailWord_40884).sum := by decide
  have hdescent : baseEnd_40884 < baseStart_40884 := by decide
  rcases family_descends (prefixWord ++ tailWord_40884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40983 : List Nat := [1, 1, 3, 5, 2, 2, 5]
def baseStart_40983 : Nat := 118140960795 + 40983 * 2 ^ 59
def prefixEnd_40983 : Nat := 4983230072969 + 3 ^ 40 * 40983 * 2
def baseEnd_40983 : Nat := 4156835093988817288697

theorem tailTrace_40983 : CollatzResearch.WordTrace tailWord_40983 prefixEnd_40983 4156835093988817288697 := by
  unfold tailWord_40983
  simp only [CollatzResearch.WordTrace]
  refine ⟨1494772810533065184263603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 996515207022043456175735 1494772810533065184263603)
  ·
    refine ⟨2242159215799597776395405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1494772810533065184263603 2242159215799597776395405)
    ·
      refine ⟨840809705924849166148277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2242159215799597776395405 840809705924849166148277)
      ·
        refine ⟨78825909930454609326401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 840809705924849166148277 78825909930454609326401)
        ·
          refine ⟨59119432447840956994801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78825909930454609326401 59119432447840956994801)
          ·
            refine ⟨44339574335880717746101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59119432447840956994801 44339574335880717746101)
            ·
              refine ⟨4156835093988817288697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44339574335880717746101 4156835093988817288697)
              ·
                rfl

theorem cell19_40983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_40983 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_40983 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_40983 prefixEnd_40983 := by exact prefixLift 40983
  have htrace : WordTrace (prefixWord ++ tailWord_40983) baseStart_40983 baseEnd_40983 := by
    simpa [prefixWord, tailWord_40983, baseEnd_40983] using wordTrace_append hprefix tailTrace_40983
  have hstable : (prefixWord ++ tailWord_40983).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40983).length < 2 ^ (prefixWord ++ tailWord_40983).sum := by decide
  have hdescent : baseEnd_40983 < baseStart_40983 := by decide
  rcases family_descends (prefixWord ++ tailWord_40983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41000 : List Nat := [2, 1, 5, 3, 1, 1, 2, 4]
def baseStart_41000 : Nat := 118140960795 + 41000 * 2 ^ 59
def prefixEnd_41000 : Nat := 4983230072969 + 3 ^ 40 * 41000 * 2
def baseEnd_41000 : Nat := 12475678124115449488267

theorem tailTrace_41000 : CollatzResearch.WordTrace tailWord_41000 prefixEnd_41000 12475678124115449488267 := by
  unfold tailWord_41000
  simp only [CollatzResearch.WordTrace]
  refine ⟨747696425735738543816227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 996928567647651391754969 747696425735738543816227)
  ·
    refine ⟨1121544638603607815724341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 747696425735738543816227 1121544638603607815724341)
    ·
      refine ⟨105144809869088232724157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1121544638603607815724341 105144809869088232724157)
      ·
        refine ⟨39429303700908087271559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105144809869088232724157 39429303700908087271559)
        ·
          refine ⟨59143955551362130907339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39429303700908087271559 59143955551362130907339)
          ·
            refine ⟨88715933327043196361009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59143955551362130907339 88715933327043196361009)
            ·
              refine ⟨66536949995282397270757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88715933327043196361009 66536949995282397270757)
              ·
                refine ⟨12475678124115449488267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66536949995282397270757 12475678124115449488267)
                ·
                  rfl

theorem cell19_41000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_41000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41000 prefixEnd_41000 := by exact prefixLift 41000
  have htrace : WordTrace (prefixWord ++ tailWord_41000) baseStart_41000 baseEnd_41000 := by
    simpa [prefixWord, tailWord_41000, baseEnd_41000] using wordTrace_append hprefix tailTrace_41000
  have hstable : (prefixWord ++ tailWord_41000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41000).length < 2 ^ (prefixWord ++ tailWord_41000).sum := by decide
  have hdescent : baseEnd_41000 < baseStart_41000 := by decide
  rcases family_descends (prefixWord ++ tailWord_41000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41002 : List Nat := [3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_41002 : Nat := 118140960795 + 41002 * 2 ^ 59
def prefixEnd_41002 : Nat := 4983230072969 + 3 ^ 40 * 41002 * 2
def baseEnd_41002 : Nat := 12476286693780037443817

theorem tailTrace_41002 : CollatzResearch.WordTrace tailWord_41002 prefixEnd_41002 12476286693780037443817 := by
  unfold tailWord_41002
  simp only [CollatzResearch.WordTrace]
  refine ⟨373866449366057857301315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 996977198309487619470173 373866449366057857301315)
  ·
    refine ⟨560799674049086785951973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 373866449366057857301315 560799674049086785951973)
    ·
      refine ⟨105149938884203772365995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 560799674049086785951973 105149938884203772365995)
      ·
        refine ⟨157724908326305658548993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105149938884203772365995 157724908326305658548993)
        ·
          refine ⟨118293681244729243911745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157724908326305658548993 118293681244729243911745)
          ·
            refine ⟨88720260933546932933809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118293681244729243911745 88720260933546932933809)
            ·
              refine ⟨66540195700160199700357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88720260933546932933809 66540195700160199700357)
              ·
                refine ⟨12476286693780037443817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66540195700160199700357 12476286693780037443817)
                ·
                  rfl

theorem cell19_41002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_41002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41002 prefixEnd_41002 := by exact prefixLift 41002
  have htrace : WordTrace (prefixWord ++ tailWord_41002) baseStart_41002 baseEnd_41002 := by
    simpa [prefixWord, tailWord_41002, baseEnd_41002] using wordTrace_append hprefix tailTrace_41002
  have hstable : (prefixWord ++ tailWord_41002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41002).length < 2 ^ (prefixWord ++ tailWord_41002).sum := by decide
  have hdescent : baseEnd_41002 < baseStart_41002 := by decide
  rcases family_descends (prefixWord ++ tailWord_41002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41042 : List Nat := [3, 2, 2, 1, 4, 7]
def baseStart_41042 : Nat := 118140960795 + 41042 * 2 ^ 59
def prefixEnd_41042 : Nat := 4983230072969 + 3 ^ 40 * 41042 * 2
def baseEnd_41042 : Nat := 1387606454119088506091

theorem tailTrace_41042 : CollatzResearch.WordTrace tailWord_41042 prefixEnd_41042 1387606454119088506091 := by
  unfold tailWord_41042
  simp only [CollatzResearch.WordTrace]
  refine ⟨374231179329829565165345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 997949811546212173774253 374231179329829565165345)
  ·
    refine ⟨280673384497372173874009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 374231179329829565165345 280673384497372173874009)
    ·
      refine ⟨210505038373029130405507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280673384497372173874009 210505038373029130405507)
      ·
        refine ⟨315757557559543695608261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210505038373029130405507 315757557559543695608261)
        ·
          refine ⟨59204542042414442926549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315757557559543695608261 59204542042414442926549)
          ·
            refine ⟨1387606454119088506091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 59204542042414442926549 1387606454119088506091)
            ·
              rfl

theorem cell19_41042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 7].length) (baseStart_41042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41042 prefixEnd_41042 := by exact prefixLift 41042
  have htrace : WordTrace (prefixWord ++ tailWord_41042) baseStart_41042 baseEnd_41042 := by
    simpa [prefixWord, tailWord_41042, baseEnd_41042] using wordTrace_append hprefix tailTrace_41042
  have hstable : (prefixWord ++ tailWord_41042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41042).length < 2 ^ (prefixWord ++ tailWord_41042).sum := by decide
  have hdescent : baseEnd_41042 < baseStart_41042 := by decide
  rcases family_descends (prefixWord ++ tailWord_41042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41061 : List Nat := [1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_41061 : Nat := 118140960795 + 41061 * 2 ^ 59
def prefixEnd_41061 : Nat := 4983230072969 + 3 ^ 40 * 41061 * 2
def baseEnd_41061 : Nat := 12494239498885382132545

theorem tailTrace_41061 : CollatzResearch.WordTrace tailWord_41061 prefixEnd_41061 12494239498885382132545 := by
  unfold tailWord_41061
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497617704250484505603037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 998411802833656337068691 1497617704250484505603037)
  ·
    refine ⟨561606639093931689601139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1497617704250484505603037 561606639093931689601139)
    ·
      refine ⟨842409958640897534401709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561606639093931689601139 842409958640897534401709)
      ·
        refine ⟨315903734490336575400641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 842409958640897534401709 315903734490336575400641)
        ·
          refine ⟨236927800867752431550481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315903734490336575400641 236927800867752431550481)
          ·
            refine ⟨177695850650814323662861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236927800867752431550481 177695850650814323662861)
            ·
              refine ⟨66635943994055371373573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177695850650814323662861 66635943994055371373573)
              ·
                refine ⟨12494239498885382132545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66635943994055371373573 12494239498885382132545)
                ·
                  rfl

theorem cell19_41061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_41061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41061 prefixEnd_41061 := by exact prefixLift 41061
  have htrace : WordTrace (prefixWord ++ tailWord_41061) baseStart_41061 baseEnd_41061 := by
    simpa [prefixWord, tailWord_41061, baseEnd_41061] using wordTrace_append hprefix tailTrace_41061
  have hstable : (prefixWord ++ tailWord_41061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41061).length < 2 ^ (prefixWord ++ tailWord_41061).sum := by decide
  have hdescent : baseEnd_41061 < baseStart_41061 := by decide
  rcases family_descends (prefixWord ++ tailWord_41061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41133 : List Nat := [1, 5, 2, 1, 2, 3, 2, 3]
def baseStart_41133 : Nat := 118140960795 + 41133 * 2 ^ 59
def prefixEnd_41133 : Nat := 4983230072969 + 3 ^ 40 * 41133 * 2
def baseEnd_41133 : Nat := 12516148006810548532349

theorem tailTrace_41133 : CollatzResearch.WordTrace tailWord_41133 prefixEnd_41133 12516148006810548532349 := by
  unfold tailWord_41133
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500243759989640802224053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1000162506659760534816035 1500243759989640802224053)
  ·
    refine ⟨140647852499028825208505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1500243759989640802224053 140647852499028825208505)
    ·
      refine ⟨105485889374271618906379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140647852499028825208505 105485889374271618906379)
      ·
        refine ⟨158228834061407428359569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105485889374271618906379 158228834061407428359569)
        ·
          refine ⟨118671625546055571269677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158228834061407428359569 118671625546055571269677)
          ·
            refine ⟨44501859579770839226129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118671625546055571269677 44501859579770839226129)
            ·
              refine ⟨33376394684828129419597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44501859579770839226129 33376394684828129419597)
              ·
                refine ⟨12516148006810548532349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33376394684828129419597 12516148006810548532349)
                ·
                  rfl

theorem cell19_41133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_41133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41133 prefixEnd_41133 := by exact prefixLift 41133
  have htrace : WordTrace (prefixWord ++ tailWord_41133) baseStart_41133 baseEnd_41133 := by
    simpa [prefixWord, tailWord_41133, baseEnd_41133] using wordTrace_append hprefix tailTrace_41133
  have hstable : (prefixWord ++ tailWord_41133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41133).length < 2 ^ (prefixWord ++ tailWord_41133).sum := by decide
  have hdescent : baseEnd_41133 < baseStart_41133 := by decide
  rcases family_descends (prefixWord ++ tailWord_41133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41156 : List Nat := [2, 3, 3, 1, 2, 1, 7]
def baseStart_41156 : Nat := 118140960795 + 41156 * 2 ^ 59
def prefixEnd_41156 : Nat := 4983230072969 + 3 ^ 40 * 41156 * 2
def baseEnd_41156 : Nat := 4174382185984436673725

theorem tailTrace_41156 : CollatzResearch.WordTrace tailWord_41156 prefixEnd_41156 4174382185984436673725 := by
  unfold tailWord_41156
  simp only [CollatzResearch.WordTrace]
  refine ⟨750541319453157865155661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1000721759270877153540881 750541319453157865155661)
  ·
    refine ⟨281452994794934199433373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 750541319453157865155661 281452994794934199433373)
    ·
      refine ⟨105544873048100324787515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281452994794934199433373 105544873048100324787515)
      ·
        refine ⟨158317309572150487181273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105544873048100324787515 158317309572150487181273)
        ·
          refine ⟨118737982179112865385955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158317309572150487181273 118737982179112865385955)
          ·
            refine ⟨178106973268669298078933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118737982179112865385955 178106973268669298078933)
            ·
              refine ⟨4174382185984436673725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 178106973268669298078933 4174382185984436673725)
              ·
                rfl

theorem cell19_41156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_41156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41156 prefixEnd_41156 := by exact prefixLift 41156
  have htrace : WordTrace (prefixWord ++ tailWord_41156) baseStart_41156 baseEnd_41156 := by
    simpa [prefixWord, tailWord_41156, baseEnd_41156] using wordTrace_append hprefix tailTrace_41156
  have hstable : (prefixWord ++ tailWord_41156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41156).length < 2 ^ (prefixWord ++ tailWord_41156).sum := by decide
  have hdescent : baseEnd_41156 < baseStart_41156 := by decide
  rcases family_descends (prefixWord ++ tailWord_41156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41173 : List Nat := [1, 3, 2, 4, 2, 1, 2, 4]
def baseStart_41173 : Nat := 118140960795 + 41173 * 2 ^ 59
def prefixEnd_41173 : Nat := 4983230072969 + 3 ^ 40 * 41173 * 2
def baseEnd_41173 : Nat := 12528319400102307643351

theorem tailTrace_41173 : CollatzResearch.WordTrace tailWord_41173 prefixEnd_41173 12528319400102307643351 := by
  unfold tailWord_41173
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501702679844727633680173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1001135119896485089120115 1501702679844727633680173)
  ·
    refine ⟨563138504941772862630065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1501702679844727633680173 563138504941772862630065)
    ·
      refine ⟨422353878706329646972549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 563138504941772862630065 422353878706329646972549)
      ·
        refine ⟨79191352257436808807353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 422353878706329646972549 79191352257436808807353)
        ·
          refine ⟨59393514193077606605515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79191352257436808807353 59393514193077606605515)
          ·
            refine ⟨89090271289616409908273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59393514193077606605515 89090271289616409908273)
            ·
              refine ⟨66817703467212307431205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89090271289616409908273 66817703467212307431205)
              ·
                refine ⟨12528319400102307643351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66817703467212307431205 12528319400102307643351)
                ·
                  rfl

theorem cell19_41173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_41173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41173 prefixEnd_41173 := by exact prefixLift 41173
  have htrace : WordTrace (prefixWord ++ tailWord_41173) baseStart_41173 baseEnd_41173 := by
    simpa [prefixWord, tailWord_41173, baseEnd_41173] using wordTrace_append hprefix tailTrace_41173
  have hstable : (prefixWord ++ tailWord_41173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41173).length < 2 ^ (prefixWord ++ tailWord_41173).sum := by decide
  have hdescent : baseEnd_41173 < baseStart_41173 := by decide
  rcases family_descends (prefixWord ++ tailWord_41173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41177 : List Nat := [1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_41177 : Nat := 118140960795 + 41177 * 2 ^ 59
def prefixEnd_41177 : Nat := 4983230072969 + 3 ^ 40 * 41177 * 2
def baseEnd_41177 : Nat := 12529536539431483554451

theorem tailTrace_41177 : CollatzResearch.WordTrace tailWord_41177 prefixEnd_41177 12529536539431483554451 := by
  unfold tailWord_41177
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501848571830236316825785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1001232381220157544550523 1501848571830236316825785)
  ·
    refine ⟨1126386428872677237619339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1501848571830236316825785 1126386428872677237619339)
    ·
      refine ⟨1689579643309015856429009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1126386428872677237619339 1689579643309015856429009)
      ·
        refine ⟨1267184732481761892321757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1689579643309015856429009 1267184732481761892321757)
        ·
          refine ⟨475194274680660709620659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1267184732481761892321757 475194274680660709620659)
          ·
            refine ⟨712791412020991064430989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475194274680660709620659 712791412020991064430989)
            ·
              refine ⟨267296779507871649161621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 712791412020991064430989 267296779507871649161621)
              ·
                refine ⟨12529536539431483554451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 267296779507871649161621 12529536539431483554451)
                ·
                  rfl

theorem cell19_41177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_41177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41177 prefixEnd_41177 := by exact prefixLift 41177
  have htrace : WordTrace (prefixWord ++ tailWord_41177) baseStart_41177 baseEnd_41177 := by
    simpa [prefixWord, tailWord_41177, baseEnd_41177] using wordTrace_append hprefix tailTrace_41177
  have hstable : (prefixWord ++ tailWord_41177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41177).length < 2 ^ (prefixWord ++ tailWord_41177).sum := by decide
  have hdescent : baseEnd_41177 < baseStart_41177 := by decide
  rcases family_descends (prefixWord ++ tailWord_41177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41196 : List Nat := [2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_41196 : Nat := 118140960795 + 41196 * 2 ^ 59
def prefixEnd_41196 : Nat := 4983230072969 + 3 ^ 40 * 41196 * 2
def baseEnd_41196 : Nat := 12535317951245069132177

theorem tailTrace_41196 : CollatzResearch.WordTrace tailWord_41196 prefixEnd_41196 12535317951245069132177 := by
  unfold tailWord_41196
  simp only [CollatzResearch.WordTrace]
  refine ⟨751270779380701280883721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1001694372507601707844961 751270779380701280883721)
  ·
    refine ⟨563453084535525960662791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 751270779380701280883721 563453084535525960662791)
    ·
      refine ⟨845179626803288940994187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563453084535525960662791 845179626803288940994187)
      ·
        refine ⟨1267769440204933411491281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 845179626803288940994187 1267769440204933411491281)
        ·
          refine ⟨950827080153700058618461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1267769440204933411491281 950827080153700058618461)
          ·
            refine ⟨356560155057637521981923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 950827080153700058618461 356560155057637521981923)
            ·
              refine ⟨534840232586456282972885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356560155057637521981923 534840232586456282972885)
              ·
                refine ⟨12535317951245069132177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 534840232586456282972885 12535317951245069132177)
                ·
                  rfl

theorem cell19_41196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_41196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41196 prefixEnd_41196 := by exact prefixLift 41196
  have htrace : WordTrace (prefixWord ++ tailWord_41196) baseStart_41196 baseEnd_41196 := by
    simpa [prefixWord, tailWord_41196, baseEnd_41196] using wordTrace_append hprefix tailTrace_41196
  have hstable : (prefixWord ++ tailWord_41196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41196).length < 2 ^ (prefixWord ++ tailWord_41196).sum := by decide
  have hdescent : baseEnd_41196 < baseStart_41196 := by decide
  rcases family_descends (prefixWord ++ tailWord_41196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41251 : List Nat := [1, 1, 1, 4, 2, 2, 5, 3]
def baseStart_41251 : Nat := 118140960795 + 41251 * 2 ^ 59
def prefixEnd_41251 : Nat := 4983230072969 + 3 ^ 40 * 41251 * 2
def baseEnd_41251 : Nat := 12552053617021237909805

theorem tailTrace_41251 : CollatzResearch.WordTrace tailWord_41251 prefixEnd_41251 12552053617021237909805 := by
  unfold tailWord_41251
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504547573562146955019607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1003031715708097970013071 1504547573562146955019607)
  ·
    refine ⟨2256821360343220432529411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1504547573562146955019607 2256821360343220432529411)
    ·
      refine ⟨3385232040514830648794117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2256821360343220432529411 3385232040514830648794117)
      ·
        refine ⟨634731007596530746648897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3385232040514830648794117 634731007596530746648897)
        ·
          refine ⟨476048255697398059986673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634731007596530746648897 476048255697398059986673)
          ·
            refine ⟨357036191773048544990005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476048255697398059986673 357036191773048544990005)
            ·
              refine ⟨33472142978723301092813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 357036191773048544990005 33472142978723301092813)
              ·
                refine ⟨12552053617021237909805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33472142978723301092813 12552053617021237909805)
                ·
                  rfl

theorem cell19_41251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_41251 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41251 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41251 prefixEnd_41251 := by exact prefixLift 41251
  have htrace : WordTrace (prefixWord ++ tailWord_41251) baseStart_41251 baseEnd_41251 := by
    simpa [prefixWord, tailWord_41251, baseEnd_41251] using wordTrace_append hprefix tailTrace_41251
  have hstable : (prefixWord ++ tailWord_41251).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41251).length < 2 ^ (prefixWord ++ tailWord_41251).sum := by decide
  have hdescent : baseEnd_41251 < baseStart_41251 := by decide
  rcases family_descends (prefixWord ++ tailWord_41251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41367 : List Nat := [1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_41367 : Nat := 118140960795 + 41367 * 2 ^ 59
def prefixEnd_41367 : Nat := 4983230072969 + 3 ^ 40 * 41367 * 2
def baseEnd_41367 : Nat := 12587350657567339331711

theorem tailTrace_41367 : CollatzResearch.WordTrace tailWord_41367 prefixEnd_41367 12587350657567339331711 := by
  unfold tailWord_41367
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508778441141898766242355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1005852294094599177494903 1508778441141898766242355)
  ·
    refine ⟨2263167661712848149363533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1508778441141898766242355 2263167661712848149363533)
    ·
      refine ⟨848687873142318056011325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2263167661712848149363533 848687873142318056011325)
      ·
        refine ⟨318257952428369271004247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 848687873142318056011325 318257952428369271004247)
        ·
          refine ⟨477386928642553906506371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318257952428369271004247 477386928642553906506371)
          ·
            refine ⟨716080392963830859759557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477386928642553906506371 716080392963830859759557)
            ·
              refine ⟨134265073680718286204917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 716080392963830859759557 134265073680718286204917)
              ·
                refine ⟨12587350657567339331711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134265073680718286204917 12587350657567339331711)
                ·
                  rfl

theorem cell19_41367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_41367 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41367 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41367 prefixEnd_41367 := by exact prefixLift 41367
  have htrace : WordTrace (prefixWord ++ tailWord_41367) baseStart_41367 baseEnd_41367 := by
    simpa [prefixWord, tailWord_41367, baseEnd_41367] using wordTrace_append hprefix tailTrace_41367
  have hstable : (prefixWord ++ tailWord_41367).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41367).length < 2 ^ (prefixWord ++ tailWord_41367).sum := by decide
  have hdescent : baseEnd_41367 < baseStart_41367 := by decide
  rcases family_descends (prefixWord ++ tailWord_41367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41384 : List Nat := [2, 1, 6, 1, 1, 8]
def baseStart_41384 : Nat := 118140960795 + 41384 * 2 ^ 59
def prefixEnd_41384 : Nat := 4983230072969 + 3 ^ 40 * 41384 * 2
def baseEnd_41384 : Nat := 1399169277746259661543

theorem tailTrace_41384 : CollatzResearch.WordTrace tailWord_41384 prefixEnd_41384 1399169277746259661543 := by
  unfold tailWord_41384
  simp only [CollatzResearch.WordTrace]
  refine ⟨754699241040155334805603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1006265654720207113074137 754699241040155334805603)
  ·
    refine ⟨1132048861560233002208405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 754699241040155334805603 1132048861560233002208405)
    ·
      refine ⟨53064790385635921978519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1132048861560233002208405 53064790385635921978519)
      ·
        refine ⟨79597185578453882967779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53064790385635921978519 79597185578453882967779)
        ·
          refine ⟨119395778367680824451669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79597185578453882967779 119395778367680824451669)
          ·
            refine ⟨1399169277746259661543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 119395778367680824451669 1399169277746259661543)
            ·
              rfl

theorem cell19_41384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 8].length) (baseStart_41384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41384 prefixEnd_41384 := by exact prefixLift 41384
  have htrace : WordTrace (prefixWord ++ tailWord_41384) baseStart_41384 baseEnd_41384 := by
    simpa [prefixWord, tailWord_41384, baseEnd_41384] using wordTrace_append hprefix tailTrace_41384
  have hstable : (prefixWord ++ tailWord_41384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41384).length < 2 ^ (prefixWord ++ tailWord_41384).sum := by decide
  have hdescent : baseEnd_41384 < baseStart_41384 := by decide
  rcases family_descends (prefixWord ++ tailWord_41384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41420 : List Nat := [2, 2, 1, 4, 3, 1, 3, 3]
def baseStart_41420 : Nat := 118140960795 + 41420 * 2 ^ 59
def prefixEnd_41420 : Nat := 4983230072969 + 3 ^ 40 * 41420 * 2
def baseEnd_41420 : Nat := 12603477753678920153789

theorem tailTrace_41420 : CollatzResearch.WordTrace tailWord_41420 prefixEnd_41420 12603477753678920153789 := by
  unfold tailWord_41420
  simp only [CollatzResearch.WordTrace]
  refine ⟨755355754974944408960857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1007141006633259211947809 755355754974944408960857)
  ·
    refine ⟨566516816231208306720643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 755355754974944408960857 566516816231208306720643)
    ·
      refine ⟨849775224346812460080965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566516816231208306720643 849775224346812460080965)
      ·
        refine ⟨159332854565027336265181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 849775224346812460080965 159332854565027336265181)
        ·
          refine ⟨59749820461885251099443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159332854565027336265181 59749820461885251099443)
          ·
            refine ⟨89624730692827876649165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59749820461885251099443 89624730692827876649165)
            ·
              refine ⟨33609274009810453743437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89624730692827876649165 33609274009810453743437)
              ·
                refine ⟨12603477753678920153789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33609274009810453743437 12603477753678920153789)
                ·
                  rfl

theorem cell19_41420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_41420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41420 prefixEnd_41420 := by exact prefixLift 41420
  have htrace : WordTrace (prefixWord ++ tailWord_41420) baseStart_41420 baseEnd_41420 := by
    simpa [prefixWord, tailWord_41420, baseEnd_41420] using wordTrace_append hprefix tailTrace_41420
  have hstable : (prefixWord ++ tailWord_41420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41420).length < 2 ^ (prefixWord ++ tailWord_41420).sum := by decide
  have hdescent : baseEnd_41420 < baseStart_41420 := by decide
  rcases family_descends (prefixWord ++ tailWord_41420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41479 : List Nat := [1, 1, 4, 3, 3, 1, 1, 5]
def baseStart_41479 : Nat := 118140960795 + 41479 * 2 ^ 59
def prefixEnd_41479 : Nat := 4983230072969 + 3 ^ 40 * 41479 * 2
def baseEnd_41479 : Nat := 12621430558784264842517

theorem tailTrace_41479 : CollatzResearch.WordTrace tailWord_41479 prefixEnd_41479 12621430558784264842517 := by
  unfold tailWord_41479
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512863416736141894319491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1008575611157427929546327 1512863416736141894319491)
  ·
    refine ⟨2269295125104212841479237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512863416736141894319491 2269295125104212841479237)
    ·
      refine ⟨425492835957039907777357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2269295125104212841479237 425492835957039907777357)
      ·
        refine ⟨159559813483889965416509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425492835957039907777357 159559813483889965416509)
        ·
          refine ⟨59834930056458737031191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159559813483889965416509 59834930056458737031191)
          ·
            refine ⟨89752395084688105546787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59834930056458737031191 89752395084688105546787)
            ·
              refine ⟨134628592627032158320181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89752395084688105546787 134628592627032158320181)
              ·
                refine ⟨12621430558784264842517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134628592627032158320181 12621430558784264842517)
                ·
                  rfl

theorem cell19_41479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_41479 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41479 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41479 prefixEnd_41479 := by exact prefixLift 41479
  have htrace : WordTrace (prefixWord ++ tailWord_41479) baseStart_41479 baseEnd_41479 := by
    simpa [prefixWord, tailWord_41479, baseEnd_41479] using wordTrace_append hprefix tailTrace_41479
  have hstable : (prefixWord ++ tailWord_41479).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41479).length < 2 ^ (prefixWord ++ tailWord_41479).sum := by decide
  have hdescent : baseEnd_41479 < baseStart_41479 := by decide
  rcases family_descends (prefixWord ++ tailWord_41479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41500 : List Nat := [2, 2, 3, 1, 2, 2, 7]
def baseStart_41500 : Nat := 118140960795 + 41500 * 2 ^ 59
def prefixEnd_41500 : Nat := 4983230072969 + 3 ^ 40 * 41500 * 2
def baseEnd_41500 : Nat := 4209273513420812791931

theorem tailTrace_41500 : CollatzResearch.WordTrace tailWord_41500 prefixEnd_41500 4209273513420812791931 := by
  unfold tailWord_41500
  simp only [CollatzResearch.WordTrace]
  refine ⟨756814674830031240416977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1009086233106708320555969 756814674830031240416977)
  ·
    refine ⟨567611006122523430312733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 756814674830031240416977 567611006122523430312733)
    ·
      refine ⟨212854127295946286367275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 567611006122523430312733 212854127295946286367275)
      ·
        refine ⟨319281190943919429550913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212854127295946286367275 319281190943919429550913)
        ·
          refine ⟨239460893207939572163185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319281190943919429550913 239460893207939572163185)
          ·
            refine ⟨179595669905954679122389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239460893207939572163185 179595669905954679122389)
            ·
              refine ⟨4209273513420812791931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 179595669905954679122389 4209273513420812791931)
              ·
                rfl

theorem cell19_41500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_41500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41500 prefixEnd_41500 := by exact prefixLift 41500
  have htrace : WordTrace (prefixWord ++ tailWord_41500) baseStart_41500 baseEnd_41500 := by
    simpa [prefixWord, tailWord_41500, baseEnd_41500] using wordTrace_append hprefix tailTrace_41500
  have hstable : (prefixWord ++ tailWord_41500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41500).length < 2 ^ (prefixWord ++ tailWord_41500).sum := by decide
  have hdescent : baseEnd_41500 < baseStart_41500 := by decide
  rcases family_descends (prefixWord ++ tailWord_41500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41566 : List Nat := [4, 4, 1, 2, 2, 1, 1, 4]
def baseStart_41566 : Nat := 118140960795 + 41566 * 2 ^ 59
def prefixEnd_41566 : Nat := 4983230072969 + 3 ^ 40 * 41566 * 2
def baseEnd_41566 : Nat := 12647903339193840908947

theorem tailTrace_41566 : CollatzResearch.WordTrace tailWord_41566 prefixEnd_41566 12647903339193840908947 := by
  unfold tailWord_41566
  simp only [CollatzResearch.WordTrace]
  refine ⟨189504570927619469092069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1010691044947303835157701 189504570927619469092069)
  ·
    refine ⟨35532107048928650454763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 189504570927619469092069 35532107048928650454763)
    ·
      refine ⟨53298160573392975682145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35532107048928650454763 53298160573392975682145)
      ·
        refine ⟨39973620430044731761609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53298160573392975682145 39973620430044731761609)
        ·
          refine ⟨29980215322533548821207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39973620430044731761609 29980215322533548821207)
          ·
            refine ⟨44970322983800323231811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29980215322533548821207 44970322983800323231811)
            ·
              refine ⟨67455484475700484847717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44970322983800323231811 67455484475700484847717)
              ·
                refine ⟨12647903339193840908947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67455484475700484847717 12647903339193840908947)
                ·
                  rfl

theorem cell19_41566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_41566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41566 prefixEnd_41566 := by exact prefixLift 41566
  have htrace : WordTrace (prefixWord ++ tailWord_41566) baseStart_41566 baseEnd_41566 := by
    simpa [prefixWord, tailWord_41566, baseEnd_41566] using wordTrace_append hprefix tailTrace_41566
  have hstable : (prefixWord ++ tailWord_41566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41566).length < 2 ^ (prefixWord ++ tailWord_41566).sum := by decide
  have hdescent : baseEnd_41566 < baseStart_41566 := by decide
  rcases family_descends (prefixWord ++ tailWord_41566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41570 : List Nat := [3, 3, 2, 3, 1, 2, 1, 4]
def baseStart_41570 : Nat := 118140960795 + 41570 * 2 ^ 59
def prefixEnd_41570 : Nat := 4983230072969 + 3 ^ 40 * 41570 * 2
def baseEnd_41570 : Nat := 12649120478523016820047

theorem tailTrace_41570 : CollatzResearch.WordTrace tailWord_41570 prefixEnd_41570 12649120478523016820047 := by
  unfold tailWord_41570
  simp only [CollatzResearch.WordTrace]
  refine ⟨379045614851616108970541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1010788306270976290588109 379045614851616108970541)
  ·
    refine ⟨142142105569356040863953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 379045614851616108970541 142142105569356040863953)
    ·
      refine ⟨106606579177017030647965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142142105569356040863953 106606579177017030647965)
      ·
        refine ⟨39977467191381386492987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106606579177017030647965 39977467191381386492987)
        ·
          refine ⟨59966200787072079739481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39977467191381386492987 59966200787072079739481)
          ·
            refine ⟨44974650590304059804611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59966200787072079739481 44974650590304059804611)
            ·
              refine ⟨67461975885456089706917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44974650590304059804611 67461975885456089706917)
              ·
                refine ⟨12649120478523016820047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67461975885456089706917 12649120478523016820047)
                ·
                  rfl

theorem cell19_41570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_41570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41570 prefixEnd_41570 := by exact prefixLift 41570
  have htrace : WordTrace (prefixWord ++ tailWord_41570) baseStart_41570 baseEnd_41570 := by
    simpa [prefixWord, tailWord_41570, baseEnd_41570] using wordTrace_append hprefix tailTrace_41570
  have hstable : (prefixWord ++ tailWord_41570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41570).length < 2 ^ (prefixWord ++ tailWord_41570).sum := by decide
  have hdescent : baseEnd_41570 < baseStart_41570 := by decide
  rcases family_descends (prefixWord ++ tailWord_41570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41593 : List Nat := [1, 2, 1, 3, 3, 3, 3, 3]
def baseStart_41593 : Nat := 118140960795 + 41593 * 2 ^ 59
def prefixEnd_41593 : Nat := 4983230072969 + 3 ^ 40 * 41593 * 2
def baseEnd_41593 : Nat := 12656119029665778308873

theorem tailTrace_41593 : CollatzResearch.WordTrace tailWord_41593 prefixEnd_41593 12656119029665778308873 := by
  unfold tailWord_41593
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517021338323139363969433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1011347558882092909312955 1517021338323139363969433)
  ·
    refine ⟨1137766003742354522977075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1517021338323139363969433 1137766003742354522977075)
    ·
      refine ⟨1706649005613531784465613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137766003742354522977075 1706649005613531784465613)
      ·
        refine ⟨639993377105074419174605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1706649005613531784465613 639993377105074419174605)
        ·
          refine ⟨239997516414402907190477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 639993377105074419174605 239997516414402907190477)
          ·
            refine ⟨89999068655401090196429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239997516414402907190477 89999068655401090196429)
            ·
              refine ⟨33749650745775408823661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89999068655401090196429 33749650745775408823661)
              ·
                refine ⟨12656119029665778308873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33749650745775408823661 12656119029665778308873)
                ·
                  rfl

theorem cell19_41593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_41593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41593 prefixEnd_41593 := by exact prefixLift 41593
  have htrace : WordTrace (prefixWord ++ tailWord_41593) baseStart_41593 baseEnd_41593 := by
    simpa [prefixWord, tailWord_41593, baseEnd_41593] using wordTrace_append hprefix tailTrace_41593
  have hstable : (prefixWord ++ tailWord_41593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41593).length < 2 ^ (prefixWord ++ tailWord_41593).sum := by decide
  have hdescent : baseEnd_41593 < baseStart_41593 := by decide
  rcases family_descends (prefixWord ++ tailWord_41593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41614 : List Nat := [4, 1, 1, 3, 1, 1, 8]
def baseStart_41614 : Nat := 118140960795 + 41614 * 2 ^ 59
def prefixEnd_41614 : Nat := 4983230072969 + 3 ^ 40 * 41614 * 2
def baseEnd_41614 : Nat := 4220836337047983947383

theorem tailTrace_41614 : CollatzResearch.WordTrace tailWord_41614 prefixEnd_41614 4220836337047983947383 := by
  unfold tailWord_41614
  simp only [CollatzResearch.WordTrace]
  refine ⟨189723408905882493810487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1011858180831373300322597 189723408905882493810487)
  ·
    refine ⟨284585113358823740715731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189723408905882493810487 284585113358823740715731)
    ·
      refine ⟨426877670038235611073597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284585113358823740715731 426877670038235611073597)
      ·
        refine ⟨160079126264338354152599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 426877670038235611073597 160079126264338354152599)
        ·
          refine ⟨240118689396507531228899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160079126264338354152599 240118689396507531228899)
          ·
            refine ⟨360178034094761296843349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240118689396507531228899 360178034094761296843349)
            ·
              refine ⟨4220836337047983947383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 360178034094761296843349 4220836337047983947383)
              ·
                rfl

theorem cell19_41614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_41614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41614 prefixEnd_41614 := by exact prefixLift 41614
  have htrace : WordTrace (prefixWord ++ tailWord_41614) baseStart_41614 baseEnd_41614 := by
    simpa [prefixWord, tailWord_41614, baseEnd_41614] using wordTrace_append hprefix tailTrace_41614
  have hstable : (prefixWord ++ tailWord_41614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41614).length < 2 ^ (prefixWord ++ tailWord_41614).sum := by decide
  have hdescent : baseEnd_41614 < baseStart_41614 := by decide
  rcases family_descends (prefixWord ++ tailWord_41614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41646 : List Nat := [4, 1, 4, 1, 1, 3, 2, 3]
def baseStart_41646 : Nat := 118140960795 + 41646 * 2 ^ 59
def prefixEnd_41646 : Nat := 4983230072969 + 3 ^ 40 * 41646 * 2
def baseEnd_41646 : Nat := 12672246125777359130951

theorem tailTrace_41646 : CollatzResearch.WordTrace tailWord_41646 prefixEnd_41646 12672246125777359130951 := by
  unfold tailWord_41646
  simp only [CollatzResearch.WordTrace]
  refine ⟨189869300891391176956099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1012636271420752943765861 189869300891391176956099)
  ·
    refine ⟨284803951337086765434149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189869300891391176956099 284803951337086765434149)
    ·
      refine ⟨53400740875703768518903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 284803951337086765434149 53400740875703768518903)
      ·
        refine ⟨80101111313555652778355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53400740875703768518903 80101111313555652778355)
        ·
          refine ⟨120151666970333479167533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80101111313555652778355 120151666970333479167533)
          ·
            refine ⟨45056875113875054687825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120151666970333479167533 45056875113875054687825)
            ·
              refine ⟨33792656335406291015869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45056875113875054687825 33792656335406291015869)
              ·
                refine ⟨12672246125777359130951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33792656335406291015869 12672246125777359130951)
                ·
                  rfl

theorem cell19_41646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_41646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41646 prefixEnd_41646 := by exact prefixLift 41646
  have htrace : WordTrace (prefixWord ++ tailWord_41646) baseStart_41646 baseEnd_41646 := by
    simpa [prefixWord, tailWord_41646, baseEnd_41646] using wordTrace_append hprefix tailTrace_41646
  have hstable : (prefixWord ++ tailWord_41646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41646).length < 2 ^ (prefixWord ++ tailWord_41646).sum := by decide
  have hdescent : baseEnd_41646 < baseStart_41646 := by decide
  rcases family_descends (prefixWord ++ tailWord_41646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41665 : List Nat := [1, 2, 6, 2, 2, 1, 5]
def baseStart_41665 : Nat := 118140960795 + 41665 * 2 ^ 59
def prefixEnd_41665 : Nat := 4983230072969 + 3 ^ 40 * 41665 * 2
def baseEnd_41665 : Nat := 4226009179196981569559

theorem tailTrace_41665 : CollatzResearch.WordTrace tailWord_41665 prefixEnd_41665 4226009179196981569559 := by
  unfold tailWord_41665
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519647394062295660590449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1013098262708197107060299 1519647394062295660590449)
  ·
    refine ⟨1139735545546721745442837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1519647394062295660590449 1139735545546721745442837)
    ·
      refine ⟨53425103697502581817633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1139735545546721745442837 53425103697502581817633)
      ·
        refine ⟨40068827773126936363225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53425103697502581817633 40068827773126936363225)
        ·
          refine ⟨30051620829845202272419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40068827773126936363225 30051620829845202272419)
          ·
            refine ⟨45077431244767803408629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30051620829845202272419 45077431244767803408629)
            ·
              refine ⟨4226009179196981569559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45077431244767803408629 4226009179196981569559)
              ·
                rfl

theorem cell19_41665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 5].length) (baseStart_41665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41665 prefixEnd_41665 := by exact prefixLift 41665
  have htrace : WordTrace (prefixWord ++ tailWord_41665) baseStart_41665 baseEnd_41665 := by
    simpa [prefixWord, tailWord_41665, baseEnd_41665] using wordTrace_append hprefix tailTrace_41665
  have hstable : (prefixWord ++ tailWord_41665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41665).length < 2 ^ (prefixWord ++ tailWord_41665).sum := by decide
  have hdescent : baseEnd_41665 < baseStart_41665 := by decide
  rcases family_descends (prefixWord ++ tailWord_41665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41690 : List Nat := [3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_41690 : Nat := 118140960795 + 41690 * 2 ^ 59
def prefixEnd_41690 : Nat := 4983230072969 + 3 ^ 40 * 41690 * 2
def baseEnd_41690 : Nat := 12685634658398294153053

theorem tailTrace_41690 : CollatzResearch.WordTrace tailWord_41690 prefixEnd_41690 12685634658398294153053 := by
  unfold tailWord_41690
  simp only [CollatzResearch.WordTrace]
  refine ⟨380139804742931232562631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1013706145981149953500349 380139804742931232562631)
  ·
    refine ⟨570209707114396848843947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 380139804742931232562631 570209707114396848843947)
    ·
      refine ⟨855314560671595273265921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570209707114396848843947 855314560671595273265921)
      ·
        refine ⟨641485920503696454949441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 855314560671595273265921 641485920503696454949441)
        ·
          refine ⟨481114440377772341212081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 641485920503696454949441 481114440377772341212081)
          ·
            refine ⟨360835830283329255909061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481114440377772341212081 360835830283329255909061)
            ·
              refine ⟨67656718178124235482949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 360835830283329255909061 67656718178124235482949)
              ·
                refine ⟨12685634658398294153053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67656718178124235482949 12685634658398294153053)
                ·
                  rfl

theorem cell19_41690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_41690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41690 prefixEnd_41690 := by exact prefixLift 41690
  have htrace : WordTrace (prefixWord ++ tailWord_41690) baseStart_41690 baseEnd_41690 := by
    simpa [prefixWord, tailWord_41690, baseEnd_41690] using wordTrace_append hprefix tailTrace_41690
  have hstable : (prefixWord ++ tailWord_41690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41690).length < 2 ^ (prefixWord ++ tailWord_41690).sum := by decide
  have hdescent : baseEnd_41690 < baseStart_41690 := by decide
  rcases family_descends (prefixWord ++ tailWord_41690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41709 : List Nat := [1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_41709 : Nat := 118140960795 + 41709 * 2 ^ 59
def prefixEnd_41709 : Nat := 4983230072969 + 3 ^ 40 * 41709 * 2
def baseEnd_41709 : Nat := 12691416070211879730779

theorem tailTrace_41709 : CollatzResearch.WordTrace tailWord_41709 prefixEnd_41709 12691416070211879730779 := by
  unfold tailWord_41709
  simp only [CollatzResearch.WordTrace]
  refine ⟨1521252205902891175192181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1014168137268594116794787 1521252205902891175192181)
  ·
    refine ⟨142617394303396047674267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1521252205902891175192181 142617394303396047674267)
    ·
      refine ⟨213926091455094071511401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142617394303396047674267 213926091455094071511401)
      ·
        refine ⟨160444568591320553633551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213926091455094071511401 160444568591320553633551)
        ·
          refine ⟨240666852886980830450327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160444568591320553633551 240666852886980830450327)
          ·
            refine ⟨361000279330471245675491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240666852886980830450327 361000279330471245675491)
            ·
              refine ⟨541500418995706868513237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361000279330471245675491 541500418995706868513237)
              ·
                refine ⟨12691416070211879730779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 541500418995706868513237 12691416070211879730779)
                ·
                  rfl

theorem cell19_41709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_41709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41709 prefixEnd_41709 := by exact prefixLift 41709
  have htrace : WordTrace (prefixWord ++ tailWord_41709) baseStart_41709 baseEnd_41709 := by
    simpa [prefixWord, tailWord_41709, baseEnd_41709] using wordTrace_append hprefix tailTrace_41709
  have hstable : (prefixWord ++ tailWord_41709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41709).length < 2 ^ (prefixWord ++ tailWord_41709).sum := by decide
  have hdescent : baseEnd_41709 < baseStart_41709 := by decide
  rcases family_descends (prefixWord ++ tailWord_41709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41838 : List Nat := [4, 1, 2, 3, 3, 1, 5]
def baseStart_41838 : Nat := 118140960795 + 41838 * 2 ^ 59
def prefixEnd_41838 : Nat := 4983230072969 + 3 ^ 40 * 41838 * 2
def baseEnd_41838 : Nat := 4243556271192600954587

theorem tailTrace_41838 : CollatzResearch.WordTrace tailWord_41838 prefixEnd_41838 4243556271192600954587 := by
  unfold tailWord_41838
  simp only [CollatzResearch.WordTrace]
  refine ⟨190744652804443275829771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1017304814957030804425445 190744652804443275829771)
  ·
    refine ⟨286116979206664913744657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190744652804443275829771 286116979206664913744657)
    ·
      refine ⟨214587734404998685308493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286116979206664913744657 214587734404998685308493)
      ·
        refine ⟨80470400401874506990685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214587734404998685308493 80470400401874506990685)
        ·
          refine ⟨30176400150702940121507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80470400401874506990685 30176400150702940121507)
          ·
            refine ⟨45264600226054410182261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30176400150702940121507 45264600226054410182261)
            ·
              refine ⟨4243556271192600954587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45264600226054410182261 4243556271192600954587)
              ·
                rfl

theorem cell19_41838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 5].length) (baseStart_41838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41838 prefixEnd_41838 := by exact prefixLift 41838
  have htrace : WordTrace (prefixWord ++ tailWord_41838) baseStart_41838 baseEnd_41838 := by
    simpa [prefixWord, tailWord_41838, baseEnd_41838] using wordTrace_append hprefix tailTrace_41838
  have hstable : (prefixWord ++ tailWord_41838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41838).length < 2 ^ (prefixWord ++ tailWord_41838).sum := by decide
  have hdescent : baseEnd_41838 < baseStart_41838 := by decide
  rcases family_descends (prefixWord ++ tailWord_41838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41861 : List Nat := [1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_41861 : Nat := 118140960795 + 41861 * 2 ^ 59
def prefixEnd_41861 : Nat := 4983230072969 + 3 ^ 40 * 41861 * 2
def baseEnd_41861 : Nat := 12737667364720564352587

theorem tailTrace_41861 : CollatzResearch.WordTrace tailWord_41861 prefixEnd_41861 12737667364720564352587 := by
  unfold tailWord_41861
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526796101352221134725437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1017864067568147423150291 1526796101352221134725437)
  ·
    refine ⟨572548538007082925522039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1526796101352221134725437 572548538007082925522039)
    ·
      refine ⟨858822807010624388283059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572548538007082925522039 858822807010624388283059)
      ·
        refine ⟨1288234210515936582424589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858822807010624388283059 1288234210515936582424589)
        ·
          refine ⟨483087828943476218409221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1288234210515936582424589 483087828943476218409221)
          ·
            refine ⟨90578967926901790951729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 483087828943476218409221 90578967926901790951729)
            ·
              refine ⟨67934225945176343213797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90578967926901790951729 67934225945176343213797)
              ·
                refine ⟨12737667364720564352587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67934225945176343213797 12737667364720564352587)
                ·
                  rfl

theorem cell19_41861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_41861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41861 prefixEnd_41861 := by exact prefixLift 41861
  have htrace : WordTrace (prefixWord ++ tailWord_41861) baseStart_41861 baseEnd_41861 := by
    simpa [prefixWord, tailWord_41861, baseEnd_41861] using wordTrace_append hprefix tailTrace_41861
  have hstable : (prefixWord ++ tailWord_41861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41861).length < 2 ^ (prefixWord ++ tailWord_41861).sum := by decide
  have hdescent : baseEnd_41861 < baseStart_41861 := by decide
  rcases family_descends (prefixWord ++ tailWord_41861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41910 : List Nat := [5, 1, 4, 1, 1, 2, 1, 4]
def baseStart_41910 : Nat := 118140960795 + 41910 * 2 ^ 59
def prefixEnd_41910 : Nat := 4983230072969 + 3 ^ 40 * 41910 * 2
def baseEnd_41910 : Nat := 12752577321502969263565

theorem tailTrace_41910 : CollatzResearch.WordTrace tailWord_41910 prefixEnd_41910 12752577321502969263565 := by
  unfold tailWord_41910
  simp only [CollatzResearch.WordTrace]
  refine ⟨95536454885918906453699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1019055518783135002172789 95536454885918906453699)
  ·
    refine ⟨143304682328878359680549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95536454885918906453699 143304682328878359680549)
    ·
      refine ⟨26869627936664692440103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143304682328878359680549 26869627936664692440103)
      ·
        refine ⟨40304441904997038660155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26869627936664692440103 40304441904997038660155)
        ·
          refine ⟨60456662857495557990233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40304441904997038660155 60456662857495557990233)
          ·
            refine ⟨45342497143121668492675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60456662857495557990233 45342497143121668492675)
            ·
              refine ⟨68013745714682502739013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45342497143121668492675 68013745714682502739013)
              ·
                refine ⟨12752577321502969263565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68013745714682502739013 12752577321502969263565)
                ·
                  rfl

theorem cell19_41910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_41910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41910 prefixEnd_41910 := by exact prefixLift 41910
  have htrace : WordTrace (prefixWord ++ tailWord_41910) baseStart_41910 baseEnd_41910 := by
    simpa [prefixWord, tailWord_41910, baseEnd_41910] using wordTrace_append hprefix tailTrace_41910
  have hstable : (prefixWord ++ tailWord_41910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41910).length < 2 ^ (prefixWord ++ tailWord_41910).sum := by decide
  have hdescent : baseEnd_41910 < baseStart_41910 := by decide
  rcases family_descends (prefixWord ++ tailWord_41910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41937 : List Nat := [1, 2, 2, 1, 2, 1, 7, 3]
def baseStart_41937 : Nat := 118140960795 + 41937 * 2 ^ 59
def prefixEnd_41937 : Nat := 4983230072969 + 3 ^ 40 * 41937 * 2
def baseEnd_41937 : Nat := 12760793011974906663491

theorem tailTrace_41937 : CollatzResearch.WordTrace tailWord_41937 prefixEnd_41937 12760793011974906663491 := by
  unfold tailWord_41937
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529568049076886114492065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1019712032717924076328043 1529568049076886114492065)
  ·
    refine ⟨1147176036807664585869049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1529568049076886114492065 1147176036807664585869049)
    ·
      refine ⟨860382027605748439401787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1147176036807664585869049 860382027605748439401787)
      ·
        refine ⟨1290573041408622659102681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860382027605748439401787 1290573041408622659102681)
        ·
          refine ⟨967929781056466994327011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290573041408622659102681 967929781056466994327011)
          ·
            refine ⟨1451894671584700491490517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967929781056466994327011 1451894671584700491490517)
            ·
              refine ⟨34028781365266417769309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1451894671584700491490517 34028781365266417769309)
              ·
                refine ⟨12760793011974906663491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34028781365266417769309 12760793011974906663491)
                ·
                  rfl

theorem cell19_41937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_41937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41937 prefixEnd_41937 := by exact prefixLift 41937
  have htrace : WordTrace (prefixWord ++ tailWord_41937) baseStart_41937 baseEnd_41937 := by
    simpa [prefixWord, tailWord_41937, baseEnd_41937] using wordTrace_append hprefix tailTrace_41937
  have hstable : (prefixWord ++ tailWord_41937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41937).length < 2 ^ (prefixWord ++ tailWord_41937).sum := by decide
  have hdescent : baseEnd_41937 < baseStart_41937 := by decide
  rcases family_descends (prefixWord ++ tailWord_41937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41954 : List Nat := [3, 3, 3, 1, 1, 2, 6]
def baseStart_41954 : Nat := 118140960795 + 41954 * 2 ^ 59
def prefixEnd_41954 : Nat := 4983230072969 + 3 ^ 40 * 41954 * 2
def baseEnd_41954 : Nat := 4255321951374634761889

theorem tailTrace_41954 : CollatzResearch.WordTrace tailWord_41954 prefixEnd_41954 4255321951374634761889 := by
  unfold tailWord_41954
  simp only [CollatzResearch.WordTrace]
  refine ⟨382547022503824504465229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1020125393343532011907277 382547022503824504465229)
  ·
    refine ⟨143455133438934189174461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 382547022503824504465229 143455133438934189174461)
    ·
      refine ⟨53795675039600320940423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143455133438934189174461 53795675039600320940423)
      ·
        refine ⟨80693512559400481410635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53795675039600320940423 80693512559400481410635)
        ·
          refine ⟨121040268839100722115953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80693512559400481410635 121040268839100722115953)
          ·
            refine ⟨90780201629325541586965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121040268839100722115953 90780201629325541586965)
            ·
              refine ⟨4255321951374634761889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90780201629325541586965 4255321951374634761889)
              ·
                rfl

theorem cell19_41954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_41954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41954 prefixEnd_41954 := by exact prefixLift 41954
  have htrace : WordTrace (prefixWord ++ tailWord_41954) baseStart_41954 baseEnd_41954 := by
    simpa [prefixWord, tailWord_41954, baseEnd_41954] using wordTrace_append hprefix tailTrace_41954
  have hstable : (prefixWord ++ tailWord_41954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41954).length < 2 ^ (prefixWord ++ tailWord_41954).sum := by decide
  have hdescent : baseEnd_41954 < baseStart_41954 := by decide
  rcases family_descends (prefixWord ++ tailWord_41954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41977 : List Nat := [1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_41977 : Nat := 118140960795 + 41977 * 2 ^ 59
def prefixEnd_41977 : Nat := 4983230072969 + 3 ^ 40 * 41977 * 2
def baseEnd_41977 : Nat := 12772964405266665774493

theorem tailTrace_41977 : CollatzResearch.WordTrace tailWord_41977 prefixEnd_41977 12772964405266665774493 := by
  unfold tailWord_41977
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531026968931972945948185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1020684645954648630632123 1531026968931972945948185)
  ·
    refine ⟨1148270226698979709461139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1531026968931972945948185 1148270226698979709461139)
    ·
      refine ⟨1722405340048469564191709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1148270226698979709461139 1722405340048469564191709)
      ·
        refine ⟨645902002518176086571891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1722405340048469564191709 645902002518176086571891)
        ·
          refine ⟨968853003777264129857837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 645902002518176086571891 968853003777264129857837)
          ·
            refine ⟨363319876416474048696689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 968853003777264129857837 363319876416474048696689)
            ·
              refine ⟨272489907312355536522517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363319876416474048696689 272489907312355536522517)
              ·
                refine ⟨12772964405266665774493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 272489907312355536522517 12772964405266665774493)
                ·
                  rfl

theorem cell19_41977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_41977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41977 prefixEnd_41977 := by exact prefixLift 41977
  have htrace : WordTrace (prefixWord ++ tailWord_41977) baseStart_41977 baseEnd_41977 := by
    simpa [prefixWord, tailWord_41977, baseEnd_41977] using wordTrace_append hprefix tailTrace_41977
  have hstable : (prefixWord ++ tailWord_41977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41977).length < 2 ^ (prefixWord ++ tailWord_41977).sum := by decide
  have hdescent : baseEnd_41977 < baseStart_41977 := by decide
  rcases family_descends (prefixWord ++ tailWord_41977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41986 : List Nat := [3, 4, 1, 3, 2, 1, 2, 3]
def baseStart_41986 : Nat := 118140960795 + 41986 * 2 ^ 59
def prefixEnd_41986 : Nat := 4983230072969 + 3 ^ 40 * 41986 * 2
def baseEnd_41986 : Nat := 12775702968757311574469

theorem tailTrace_41986 : CollatzResearch.WordTrace tailWord_41986 prefixEnd_41986 12775702968757311574469 := by
  unfold tailWord_41986
  simp only [CollatzResearch.WordTrace]
  refine ⟨382838806474841870756453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1020903483932911655350541 382838806474841870756453)
  ·
    refine ⟨71782276214032850766835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 382838806474841870756453 71782276214032850766835)
    ·
      refine ⟨107673414321049276150253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71782276214032850766835 107673414321049276150253)
      ·
        refine ⟨40377530370393478556345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107673414321049276150253 40377530370393478556345)
        ·
          refine ⟨30283147777795108917259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40377530370393478556345 30283147777795108917259)
          ·
            refine ⟨45424721666692663375889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30283147777795108917259 45424721666692663375889)
            ·
              refine ⟨34068541250019497531917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45424721666692663375889 34068541250019497531917)
              ·
                refine ⟨12775702968757311574469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34068541250019497531917 12775702968757311574469)
                ·
                  rfl

theorem cell19_41986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_41986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41986 prefixEnd_41986 := by exact prefixLift 41986
  have htrace : WordTrace (prefixWord ++ tailWord_41986) baseStart_41986 baseEnd_41986 := by
    simpa [prefixWord, tailWord_41986, baseEnd_41986] using wordTrace_append hprefix tailTrace_41986
  have hstable : (prefixWord ++ tailWord_41986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41986).length < 2 ^ (prefixWord ++ tailWord_41986).sum := by decide
  have hdescent : baseEnd_41986 < baseStart_41986 := by decide
  rcases family_descends (prefixWord ++ tailWord_41986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41992 : List Nat := [2, 1, 3, 2, 1, 5, 2, 3]
def baseStart_41992 : Nat := 118140960795 + 41992 * 2 ^ 59
def prefixEnd_41992 : Nat := 4983230072969 + 3 ^ 40 * 41992 * 2
def baseEnd_41992 : Nat := 12777528677751075441119

theorem tailTrace_41992 : CollatzResearch.WordTrace tailWord_41992 prefixEnd_41992 12777528677751075441119 := by
  unfold tailWord_41992
  simp only [CollatzResearch.WordTrace]
  refine ⟨765787031938815253872115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1021049375918420338496153 765787031938815253872115)
  ·
    refine ⟨1148680547908222880808173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 765787031938815253872115 1148680547908222880808173)
    ·
      refine ⟨430755205465583580303065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1148680547908222880808173 430755205465583580303065)
      ·
        refine ⟨323066404099187685227299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430755205465583580303065 323066404099187685227299)
        ·
          refine ⟨484599606148781527840949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323066404099187685227299 484599606148781527840949)
          ·
            refine ⟨45431213076448268235089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 484599606148781527840949 45431213076448268235089)
            ·
              refine ⟨34073409807336201176317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45431213076448268235089 34073409807336201176317)
              ·
                refine ⟨12777528677751075441119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34073409807336201176317 12777528677751075441119)
                ·
                  rfl

theorem cell19_41992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_41992 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41992 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41992 prefixEnd_41992 := by exact prefixLift 41992
  have htrace : WordTrace (prefixWord ++ tailWord_41992) baseStart_41992 baseEnd_41992 := by
    simpa [prefixWord, tailWord_41992, baseEnd_41992] using wordTrace_append hprefix tailTrace_41992
  have hstable : (prefixWord ++ tailWord_41992).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41992).length < 2 ^ (prefixWord ++ tailWord_41992).sum := by decide
  have hdescent : baseEnd_41992 < baseStart_41992 := by decide
  rcases family_descends (prefixWord ++ tailWord_41992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_41994 : List Nat := [3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_41994 : Nat := 118140960795 + 41994 * 2 ^ 59
def prefixEnd_41994 : Nat := 4983230072969 + 3 ^ 40 * 41994 * 2
def baseEnd_41994 : Nat := 12778137247415663396669

theorem tailTrace_41994 : CollatzResearch.WordTrace tailWord_41994 prefixEnd_41994 12778137247415663396669 := by
  unfold tailWord_41994
  simp only [CollatzResearch.WordTrace]
  refine ⟨382911752467596212329259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1021098006580256566211357 382911752467596212329259)
  ·
    refine ⟨574367628701394318493889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 382911752467596212329259 574367628701394318493889)
    ·
      refine ⟨430775721526045738870417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 574367628701394318493889 430775721526045738870417)
      ·
        refine ⟨323081791144534304152813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430775721526045738870417 323081791144534304152813)
        ·
          refine ⟨121155671679200364057305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323081791144534304152813 121155671679200364057305)
          ·
            refine ⟨90866753759400273042979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121155671679200364057305 90866753759400273042979)
            ·
              refine ⟨136300130639100409564469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90866753759400273042979 136300130639100409564469)
              ·
                refine ⟨12778137247415663396669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136300130639100409564469 12778137247415663396669)
                ·
                  rfl

theorem cell19_41994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_41994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_41994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_41994 prefixEnd_41994 := by exact prefixLift 41994
  have htrace : WordTrace (prefixWord ++ tailWord_41994) baseStart_41994 baseEnd_41994 := by
    simpa [prefixWord, tailWord_41994, baseEnd_41994] using wordTrace_append hprefix tailTrace_41994
  have hstable : (prefixWord ++ tailWord_41994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_41994).length < 2 ^ (prefixWord ++ tailWord_41994).sum := by decide
  have hdescent : baseEnd_41994 < baseStart_41994 := by decide
  rcases family_descends (prefixWord ++ tailWord_41994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42015 : List Nat := [1, 1, 2, 4, 1, 3, 7]
def baseStart_42015 : Nat := 118140960795 + 42015 * 2 ^ 59
def prefixEnd_42015 : Nat := 4983230072969 + 3 ^ 40 * 42015 * 2
def baseEnd_42015 : Nat := 4261509076297945643315

theorem tailTrace_42015 : CollatzResearch.WordTrace tailWord_42015 prefixEnd_42015 4261509076297945643315 := by
  unfold tailWord_42015
  simp only [CollatzResearch.WordTrace]
  refine ⟨1532412942794305435831499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1021608628529536957220999 1532412942794305435831499)
  ·
    refine ⟨2298619414191458153747249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1532412942794305435831499 2298619414191458153747249)
    ·
      refine ⟨1723964560643593615310437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2298619414191458153747249 1723964560643593615310437)
      ·
        refine ⟨323243355120673802870707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1723964560643593615310437 323243355120673802870707)
        ·
          refine ⟨484865032681010704306061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323243355120673802870707 484865032681010704306061)
          ·
            refine ⟨181824387255379014114773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 484865032681010704306061 181824387255379014114773)
            ·
              refine ⟨4261509076297945643315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 181824387255379014114773 4261509076297945643315)
              ·
                rfl

theorem cell19_42015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_42015 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42015 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42015 prefixEnd_42015 := by exact prefixLift 42015
  have htrace : WordTrace (prefixWord ++ tailWord_42015) baseStart_42015 baseEnd_42015 := by
    simpa [prefixWord, tailWord_42015, baseEnd_42015] using wordTrace_append hprefix tailTrace_42015
  have hstable : (prefixWord ++ tailWord_42015).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42015).length < 2 ^ (prefixWord ++ tailWord_42015).sum := by decide
  have hdescent : baseEnd_42015 < baseStart_42015 := by decide
  rcases family_descends (prefixWord ++ tailWord_42015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42053 : List Nat := [1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_42053 : Nat := 118140960795 + 42053 * 2 ^ 59
def prefixEnd_42053 : Nat := 4983230072969 + 3 ^ 40 * 42053 * 2
def baseEnd_42053 : Nat := 12796090052521008085397

theorem tailTrace_42053 : CollatzResearch.WordTrace tailWord_42053 prefixEnd_42053 12796090052521008085397 := by
  unfold tailWord_42053
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533798916656637925714813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1022532611104425283809875 1533798916656637925714813)
  ·
    refine ⟨575174593746239222143055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1533798916656637925714813 575174593746239222143055)
    ·
      refine ⟨862761890619358833214583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575174593746239222143055 862761890619358833214583)
      ·
        refine ⟨1294142835929038249821875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862761890619358833214583 1294142835929038249821875)
        ·
          refine ⟨1941214253893557374732813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294142835929038249821875 1941214253893557374732813)
          ·
            refine ⟨727955345210084015524805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1941214253893557374732813 727955345210084015524805)
            ·
              refine ⟨136491627226890752910901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 727955345210084015524805 136491627226890752910901)
              ·
                refine ⟨12796090052521008085397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136491627226890752910901 12796090052521008085397)
                ·
                  rfl

theorem cell19_42053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_42053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42053 prefixEnd_42053 := by exact prefixLift 42053
  have htrace : WordTrace (prefixWord ++ tailWord_42053) baseStart_42053 baseEnd_42053 := by
    simpa [prefixWord, tailWord_42053, baseEnd_42053] using wordTrace_append hprefix tailTrace_42053
  have hstable : (prefixWord ++ tailWord_42053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42053).length < 2 ^ (prefixWord ++ tailWord_42053).sum := by decide
  have hdescent : baseEnd_42053 < baseStart_42053 := by decide
  rcases family_descends (prefixWord ++ tailWord_42053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42089 : List Nat := [1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_42089 : Nat := 118140960795 + 42089 * 2 ^ 59
def prefixEnd_42089 : Nat := 4983230072969 + 3 ^ 40 * 42089 * 2
def baseEnd_42089 : Nat := 12807044306483591285299

theorem tailTrace_42089 : CollatzResearch.WordTrace tailWord_42089 prefixEnd_42089 12807044306483591285299 := by
  unfold tailWord_42089
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535111944526216074025321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1023407963017477382683547 1535111944526216074025321)
  ·
    refine ⟨1151333958394662055518991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1535111944526216074025321 1151333958394662055518991)
    ·
      refine ⟨1727000937591993083278487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151333958394662055518991 1727000937591993083278487)
      ·
        refine ⟨2590501406387989624917731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727000937591993083278487 2590501406387989624917731)
        ·
          refine ⟨3885752109581984437376597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590501406387989624917731 3885752109581984437376597)
          ·
            refine ⟨45536157534163880125507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 3885752109581984437376597 45536157534163880125507)
            ·
              refine ⟨68304236301245820188261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45536157534163880125507 68304236301245820188261)
              ·
                refine ⟨12807044306483591285299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68304236301245820188261 12807044306483591285299)
                ·
                  rfl

theorem cell19_42089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_42089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42089 prefixEnd_42089 := by exact prefixLift 42089
  have htrace : WordTrace (prefixWord ++ tailWord_42089) baseStart_42089 baseEnd_42089 := by
    simpa [prefixWord, tailWord_42089, baseEnd_42089] using wordTrace_append hprefix tailTrace_42089
  have hstable : (prefixWord ++ tailWord_42089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42089).length < 2 ^ (prefixWord ++ tailWord_42089).sum := by decide
  have hdescent : baseEnd_42089 < baseStart_42089 := by decide
  rcases family_descends (prefixWord ++ tailWord_42089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42108 : List Nat := [2, 2, 2, 1, 1, 3, 5, 3]
def baseStart_42108 : Nat := 118140960795 + 42108 * 2 ^ 59
def prefixEnd_42108 : Nat := 4983230072969 + 3 ^ 40 * 42108 * 2
def baseEnd_42108 : Nat := 12812825718297176863025

theorem tailTrace_42108 : CollatzResearch.WordTrace tailWord_42108 prefixEnd_42108 12812825718297176863025 := by
  unfold tailWord_42108
  simp only [CollatzResearch.WordTrace]
  refine ⟨767902465728691159483489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1023869954304921545977985 767902465728691159483489)
  ·
    refine ⟨575926849296518369612617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 767902465728691159483489 575926849296518369612617)
    ·
      refine ⟨431945136972388777209463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 575926849296518369612617 431945136972388777209463)
      ·
        refine ⟨647917705458583165814195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431945136972388777209463 647917705458583165814195)
        ·
          refine ⟨971876558187874748721293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647917705458583165814195 971876558187874748721293)
          ·
            refine ⟨364453709320453030770485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 971876558187874748721293 364453709320453030770485)
            ·
              refine ⟨34167535248792471634733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 364453709320453030770485 34167535248792471634733)
              ·
                refine ⟨12812825718297176863025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34167535248792471634733 12812825718297176863025)
                ·
                  rfl

theorem cell19_42108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_42108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42108 prefixEnd_42108 := by exact prefixLift 42108
  have htrace : WordTrace (prefixWord ++ tailWord_42108) baseStart_42108 baseEnd_42108 := by
    simpa [prefixWord, tailWord_42108, baseEnd_42108] using wordTrace_append hprefix tailTrace_42108
  have hstable : (prefixWord ++ tailWord_42108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42108).length < 2 ^ (prefixWord ++ tailWord_42108).sum := by decide
  have hdescent : baseEnd_42108 < baseStart_42108 := by decide
  rcases family_descends (prefixWord ++ tailWord_42108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42167 : List Nat := [1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_42167 : Nat := 118140960795 + 42167 * 2 ^ 59
def prefixEnd_42167 : Nat := 4983230072969 + 3 ^ 40 * 42167 * 2
def baseEnd_42167 : Nat := 12830778523402521551753

theorem tailTrace_42167 : CollatzResearch.WordTrace tailWord_42167 prefixEnd_42167 12830778523402521551753 := by
  unfold tailWord_42167
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537956838243635395364755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1025304558829090263576503 1537956838243635395364755)
  ·
    refine ⟨2306935257365453093047133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1537956838243635395364755 2306935257365453093047133)
    ·
      refine ⟨865100721512044909892675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2306935257365453093047133 865100721512044909892675)
      ·
        refine ⟨1297651082268067364839013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865100721512044909892675 1297651082268067364839013)
        ·
          refine ⟨243309577925262630907315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1297651082268067364839013 243309577925262630907315)
          ·
            refine ⟨364964366887893946360973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243309577925262630907315 364964366887893946360973)
            ·
              refine ⟨136861637582960229885365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364964366887893946360973 136861637582960229885365)
              ·
                refine ⟨12830778523402521551753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136861637582960229885365 12830778523402521551753)
                ·
                  rfl

theorem cell19_42167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_42167 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42167 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42167 prefixEnd_42167 := by exact prefixLift 42167
  have htrace : WordTrace (prefixWord ++ tailWord_42167) baseStart_42167 baseEnd_42167 := by
    simpa [prefixWord, tailWord_42167, baseEnd_42167] using wordTrace_append hprefix tailTrace_42167
  have hstable : (prefixWord ++ tailWord_42167).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42167).length < 2 ^ (prefixWord ++ tailWord_42167).sum := by decide
  have hdescent : baseEnd_42167 < baseStart_42167 := by decide
  rcases family_descends (prefixWord ++ tailWord_42167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42178 : List Nat := [3, 5, 1, 1, 3, 1, 5]
def baseStart_42178 : Nat := 118140960795 + 42178 * 2 ^ 59
def prefixEnd_42178 : Nat := 4983230072969 + 3 ^ 40 * 42178 * 2
def baseEnd_42178 : Nat := 4278041885519251769093

theorem tailTrace_42178 : CollatzResearch.WordTrace tailWord_42178 prefixEnd_42178 4278041885519251769093 := by
  unfold tailWord_42178
  simp only [CollatzResearch.WordTrace]
  refine ⟨384589510300946068503797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1025572027469189516010125 384589510300946068503797)
  ·
    refine ⟨36055266590713693922231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 384589510300946068503797 36055266590713693922231)
    ·
      refine ⟨54082899886070540883347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36055266590713693922231 54082899886070540883347)
      ·
        refine ⟨81124349829105811325021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54082899886070540883347 81124349829105811325021)
        ·
          refine ⟨30421631185914679246883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81124349829105811325021 30421631185914679246883)
          ·
            refine ⟨45632446778872018870325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30421631185914679246883 45632446778872018870325)
            ·
              refine ⟨4278041885519251769093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45632446778872018870325 4278041885519251769093)
              ·
                rfl

theorem cell19_42178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 5].length) (baseStart_42178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42178 prefixEnd_42178 := by exact prefixLift 42178
  have htrace : WordTrace (prefixWord ++ tailWord_42178) baseStart_42178 baseEnd_42178 := by
    simpa [prefixWord, tailWord_42178, baseEnd_42178] using wordTrace_append hprefix tailTrace_42178
  have hstable : (prefixWord ++ tailWord_42178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42178).length < 2 ^ (prefixWord ++ tailWord_42178).sum := by decide
  have hdescent : baseEnd_42178 < baseStart_42178 := by decide
  rcases family_descends (prefixWord ++ tailWord_42178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42186 : List Nat := [3, 1, 2, 1, 3, 2, 7]
def baseStart_42186 : Nat := 118140960795 + 42186 * 2 ^ 59
def prefixEnd_42186 : Nat := 4983230072969 + 3 ^ 40 * 42186 * 2
def baseEnd_42186 : Nat := 4278853311738702376493

theorem tailTrace_42186 : CollatzResearch.WordTrace tailWord_42186 prefixEnd_42186 4278853311738702376493 := by
  unfold tailWord_42186
  simp only [CollatzResearch.WordTrace]
  refine ⟨384662456293700410076603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1025766550116534426870941 384662456293700410076603)
  ·
    refine ⟨576993684440550615114905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384662456293700410076603 576993684440550615114905)
    ·
      refine ⟨432745263330412961336179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 576993684440550615114905 432745263330412961336179)
      ·
        refine ⟨649117894995619442004269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432745263330412961336179 649117894995619442004269)
        ·
          refine ⟨243419210623357290751601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 649117894995619442004269 243419210623357290751601)
          ·
            refine ⟨182564407967517968063701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243419210623357290751601 182564407967517968063701)
            ·
              refine ⟨4278853311738702376493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 182564407967517968063701 4278853311738702376493)
              ·
                rfl

theorem cell19_42186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_42186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42186 prefixEnd_42186 := by exact prefixLift 42186
  have htrace : WordTrace (prefixWord ++ tailWord_42186) baseStart_42186 baseEnd_42186 := by
    simpa [prefixWord, tailWord_42186, baseEnd_42186] using wordTrace_append hprefix tailTrace_42186
  have hstable : (prefixWord ++ tailWord_42186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42186).length < 2 ^ (prefixWord ++ tailWord_42186).sum := by decide
  have hdescent : baseEnd_42186 < baseStart_42186 := by decide
  rcases family_descends (prefixWord ++ tailWord_42186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42300 : List Nat := [2, 2, 2, 2, 1, 4, 6]
def baseStart_42300 : Nat := 118140960795 + 42300 * 2 ^ 59
def prefixEnd_42300 : Nat := 4983230072969 + 3 ^ 40 * 42300 * 2
def baseEnd_42300 : Nat := 4290416135365873531945

theorem tailTrace_42300 : CollatzResearch.WordTrace tailWord_42300 prefixEnd_42300 4290416135365873531945 := by
  unfold tailWord_42300
  simp only [CollatzResearch.WordTrace]
  refine ⟨771403873380899554978177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1028538497841199406637569 771403873380899554978177)
  ·
    refine ⟨578552905035674666233633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 771403873380899554978177 578552905035674666233633)
    ·
      refine ⟨433914678776755999675225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 578552905035674666233633 433914678776755999675225)
      ·
        refine ⟨325436009082566999756419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433914678776755999675225 325436009082566999756419)
        ·
          refine ⟨488154013623850499634629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325436009082566999756419 488154013623850499634629)
          ·
            refine ⟨91528877554471968681493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 488154013623850499634629 91528877554471968681493)
            ·
              refine ⟨4290416135365873531945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91528877554471968681493 4290416135365873531945)
              ·
                rfl

theorem cell19_42300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_42300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42300 prefixEnd_42300 := by exact prefixLift 42300
  have htrace : WordTrace (prefixWord ++ tailWord_42300) baseStart_42300 baseEnd_42300 := by
    simpa [prefixWord, tailWord_42300, baseEnd_42300] using wordTrace_append hprefix tailTrace_42300
  have hstable : (prefixWord ++ tailWord_42300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42300).length < 2 ^ (prefixWord ++ tailWord_42300).sum := by decide
  have hdescent : baseEnd_42300 < baseStart_42300 := by decide
  rcases family_descends (prefixWord ++ tailWord_42300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42326 : List Nat := [5, 2, 3, 1, 2, 1, 2, 3]
def baseStart_42326 : Nat := 118140960795 + 42326 * 2 ^ 59
def prefixEnd_42326 : Nat := 4983230072969 + 3 ^ 40 * 42326 * 2
def baseEnd_42326 : Nat := 12879159811737264017987

theorem tailTrace_42326 : CollatzResearch.WordTrace tailWord_42326 prefixEnd_42326 12879159811737264017987 := by
  unfold tailWord_42326
  simp only [CollatzResearch.WordTrace]
  refine ⟨96484752791725346900177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1029170696445070366935221 96484752791725346900177)
  ·
    refine ⟨72363564593794010175133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96484752791725346900177 72363564593794010175133)
    ·
      refine ⟨27136336722672753815675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72363564593794010175133 27136336722672753815675)
      ·
        refine ⟨40704505084009130723513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27136336722672753815675 40704505084009130723513)
        ·
          refine ⟨30528378813006848042635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40704505084009130723513 30528378813006848042635)
          ·
            refine ⟨45792568219510272063953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30528378813006848042635 45792568219510272063953)
            ·
              refine ⟨34344426164632704047965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45792568219510272063953 34344426164632704047965)
              ·
                refine ⟨12879159811737264017987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34344426164632704047965 12879159811737264017987)
                ·
                  rfl

theorem cell19_42326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_42326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42326 prefixEnd_42326 := by exact prefixLift 42326
  have htrace : WordTrace (prefixWord ++ tailWord_42326) baseStart_42326 baseEnd_42326 := by
    simpa [prefixWord, tailWord_42326, baseEnd_42326] using wordTrace_append hprefix tailTrace_42326
  have hstable : (prefixWord ++ tailWord_42326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42326).length < 2 ^ (prefixWord ++ tailWord_42326).sum := by decide
  have hdescent : baseEnd_42326 < baseStart_42326 := by decide
  rcases family_descends (prefixWord ++ tailWord_42326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42336 : List Nat := [2, 1, 1, 3, 4, 1, 4, 3]
def baseStart_42336 : Nat := 118140960795 + 42336 * 2 ^ 59
def prefixEnd_42336 : Nat := 4983230072969 + 3 ^ 40 * 42336 * 2
def baseEnd_42336 : Nat := 12882202660060203795737

theorem tailTrace_42336 : CollatzResearch.WordTrace tailWord_42336 prefixEnd_42336 12882202660060203795737 := by
  unfold tailWord_42336
  simp only [CollatzResearch.WordTrace]
  refine ⟨772060387315688629133431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1029413849754251505511241 772060387315688629133431)
  ·
    refine ⟨1158090580973532943700147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 772060387315688629133431 1158090580973532943700147)
    ·
      refine ⟨1737135871460299415550221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158090580973532943700147 1737135871460299415550221)
      ·
        refine ⟨651425951797612280831333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1737135871460299415550221 651425951797612280831333)
        ·
          refine ⟨122142365962052302655875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 651425951797612280831333 122142365962052302655875)
          ·
            refine ⟨183213548943078453983813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122142365962052302655875 183213548943078453983813)
            ·
              refine ⟨34352540426827210121965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183213548943078453983813 34352540426827210121965)
              ·
                refine ⟨12882202660060203795737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34352540426827210121965 12882202660060203795737)
                ·
                  rfl

theorem cell19_42336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_42336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42336 prefixEnd_42336 := by exact prefixLift 42336
  have htrace : WordTrace (prefixWord ++ tailWord_42336) baseStart_42336 baseEnd_42336 := by
    simpa [prefixWord, tailWord_42336, baseEnd_42336] using wordTrace_append hprefix tailTrace_42336
  have hstable : (prefixWord ++ tailWord_42336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42336).length < 2 ^ (prefixWord ++ tailWord_42336).sum := by decide
  have hdescent : baseEnd_42336 < baseStart_42336 := by decide
  rcases family_descends (prefixWord ++ tailWord_42336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42376 : List Nat := [2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_42376 : Nat := 118140960795 + 42376 * 2 ^ 59
def prefixEnd_42376 : Nat := 4983230072969 + 3 ^ 40 * 42376 * 2
def baseEnd_42376 : Nat := 12894374053351962906739

theorem tailTrace_42376 : CollatzResearch.WordTrace tailWord_42376 prefixEnd_42376 12894374053351962906739 := by
  unfold tailWord_42376
  simp only [CollatzResearch.WordTrace]
  refine ⟨772789847243232044861491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1030386462990976059815321 772789847243232044861491)
  ·
    refine ⟨1159184770864848067292237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 772789847243232044861491 1159184770864848067292237)
    ·
      refine ⟨434694289074318025234589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1159184770864848067292237 434694289074318025234589)
      ·
        refine ⟨163010358402869259462971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 434694289074318025234589 163010358402869259462971)
        ·
          refine ⟨244515537604303889194457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163010358402869259462971 244515537604303889194457)
          ·
            refine ⟨183386653203227916895843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244515537604303889194457 183386653203227916895843)
            ·
              refine ⟨275079979804841875343765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183386653203227916895843 275079979804841875343765)
              ·
                refine ⟨12894374053351962906739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 275079979804841875343765 12894374053351962906739)
                ·
                  rfl

theorem cell19_42376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_42376 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42376 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42376 prefixEnd_42376 := by exact prefixLift 42376
  have htrace : WordTrace (prefixWord ++ tailWord_42376) baseStart_42376 baseEnd_42376 := by
    simpa [prefixWord, tailWord_42376, baseEnd_42376] using wordTrace_append hprefix tailTrace_42376
  have hstable : (prefixWord ++ tailWord_42376).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42376).length < 2 ^ (prefixWord ++ tailWord_42376).sum := by decide
  have hdescent : baseEnd_42376 < baseStart_42376 := by decide
  rcases family_descends (prefixWord ++ tailWord_42376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42471 : List Nat := [1, 1, 5, 2, 1, 3, 6]
def baseStart_42471 : Nat := 118140960795 + 42471 * 2 ^ 59
def prefixEnd_42471 : Nat := 4983230072969 + 3 ^ 40 * 42471 * 2
def baseEnd_42471 : Nat := 4307760370806630265123

theorem tailTrace_42471 : CollatzResearch.WordTrace tailWord_42471 prefixEnd_42471 4307760370806630265123 := by
  unfold tailWord_42471
  simp only [CollatzResearch.WordTrace]
  refine ⟨1549044629142295314431267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1032696419428196876287511 1549044629142295314431267)
  ·
    refine ⟨2323566943713442971646901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1549044629142295314431267 2323566943713442971646901)
    ·
      refine ⟨217834400973135278591897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2323566943713442971646901 217834400973135278591897)
      ·
        refine ⟨163375800729851458943923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217834400973135278591897 163375800729851458943923)
        ·
          refine ⟨245063701094777188415885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163375800729851458943923 245063701094777188415885)
          ·
            refine ⟨91898887910541445655957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245063701094777188415885 91898887910541445655957)
            ·
              refine ⟨4307760370806630265123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91898887910541445655957 4307760370806630265123)
              ·
                rfl

theorem cell19_42471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 6].length) (baseStart_42471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42471 prefixEnd_42471 := by exact prefixLift 42471
  have htrace : WordTrace (prefixWord ++ tailWord_42471) baseStart_42471 baseEnd_42471 := by
    simpa [prefixWord, tailWord_42471, baseEnd_42471] using wordTrace_append hprefix tailTrace_42471
  have hstable : (prefixWord ++ tailWord_42471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42471).length < 2 ^ (prefixWord ++ tailWord_42471).sum := by decide
  have hdescent : baseEnd_42471 < baseStart_42471 := by decide
  rcases family_descends (prefixWord ++ tailWord_42471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42528 : List Nat := [2, 1, 1, 6, 1, 1, 7]
def baseStart_42528 : Nat := 118140960795 + 42528 * 2 ^ 59
def prefixEnd_42528 : Nat := 4983230072969 + 3 ^ 40 * 42528 * 2
def baseEnd_42528 : Nat := 4313541782620215842849

theorem tailTrace_42528 : CollatzResearch.WordTrace tailWord_42528 prefixEnd_42528 4313541782620215842849 := by
  unfold tailWord_42528
  simp only [CollatzResearch.WordTrace]
  refine ⟨775561794967897024628119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1034082393290529366170825 775561794967897024628119)
  ·
    refine ⟨1163342692451845536942179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 775561794967897024628119 1163342692451845536942179)
    ·
      refine ⟨1745014038677768305413269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1163342692451845536942179 1745014038677768305413269)
      ·
        refine ⟨81797533063020389316247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1745014038677768305413269 81797533063020389316247)
        ·
          refine ⟨122696299594530583974371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81797533063020389316247 122696299594530583974371)
          ·
            refine ⟨184044449391795875961557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122696299594530583974371 184044449391795875961557)
            ·
              refine ⟨4313541782620215842849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 184044449391795875961557 4313541782620215842849)
              ·
                rfl

theorem cell19_42528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_42528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42528 prefixEnd_42528 := by exact prefixLift 42528
  have htrace : WordTrace (prefixWord ++ tailWord_42528) baseStart_42528 baseEnd_42528 := by
    simpa [prefixWord, tailWord_42528, baseEnd_42528] using wordTrace_append hprefix tailTrace_42528
  have hstable : (prefixWord ++ tailWord_42528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42528).length < 2 ^ (prefixWord ++ tailWord_42528).sum := by decide
  have hdescent : baseEnd_42528 < baseStart_42528 := by decide
  rcases family_descends (prefixWord ++ tailWord_42528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42547 : List Nat := [1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_42547 : Nat := 118140960795 + 42547 * 2 ^ 59
def prefixEnd_42547 : Nat := 4983230072969 + 3 ^ 40 * 42547 * 2
def baseEnd_42547 : Nat := 12946406759674233106273

theorem tailTrace_42547 : CollatzResearch.WordTrace tailWord_42547 prefixEnd_42547 12946406759674233106273 := by
  unfold tailWord_42547
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551816576866960294197895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1034544384577973529465263 1551816576866960294197895)
  ·
    refine ⟨2327724865300440441296843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1551816576866960294197895 2327724865300440441296843)
    ·
      refine ⟨3491587297950660661945265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2327724865300440441296843 3491587297950660661945265)
      ·
        refine ⟨2618690473462995496458949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3491587297950660661945265 2618690473462995496458949)
        ·
          refine ⟨491004463774311655586053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2618690473462995496458949 491004463774311655586053)
          ·
            refine ⟨92063336957683435422385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 491004463774311655586053 92063336957683435422385)
            ·
              refine ⟨69047502718262576566789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92063336957683435422385 69047502718262576566789)
              ·
                refine ⟨12946406759674233106273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69047502718262576566789 12946406759674233106273)
                ·
                  rfl

theorem cell19_42547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_42547 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42547 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42547 prefixEnd_42547 := by exact prefixLift 42547
  have htrace : WordTrace (prefixWord ++ tailWord_42547) baseStart_42547 baseEnd_42547 := by
    simpa [prefixWord, tailWord_42547, baseEnd_42547] using wordTrace_append hprefix tailTrace_42547
  have hstable : (prefixWord ++ tailWord_42547).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42547).length < 2 ^ (prefixWord ++ tailWord_42547).sum := by decide
  have hdescent : baseEnd_42547 < baseStart_42547 := by decide
  rcases family_descends (prefixWord ++ tailWord_42547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42602 : List Nat := [3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_42602 : Nat := 118140960795 + 42602 * 2 ^ 59
def prefixEnd_42602 : Nat := 4983230072969 + 3 ^ 40 * 42602 * 2
def baseEnd_42602 : Nat := 12963142425450401883901

theorem tailTrace_42602 : CollatzResearch.WordTrace tailWord_42602 prefixEnd_42602 12963142425450401883901 := by
  unfold tailWord_42602
  simp only [CollatzResearch.WordTrace]
  refine ⟨388455647916926171862515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1035881727778469791633373 388455647916926171862515)
  ·
    refine ⟨582683471875389257793773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 388455647916926171862515 582683471875389257793773)
    ·
      refine ⟨218506301953270971672665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 582683471875389257793773 218506301953270971672665)
      ·
        refine ⟨163879726464953228754499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218506301953270971672665 163879726464953228754499)
        ·
          refine ⟨245819589697429843131749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163879726464953228754499 245819589697429843131749)
          ·
            refine ⟨46091173068268095587203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245819589697429843131749 46091173068268095587203)
            ·
              refine ⟨69136759602402143380805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46091173068268095587203 69136759602402143380805)
              ·
                refine ⟨12963142425450401883901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69136759602402143380805 12963142425450401883901)
                ·
                  rfl

theorem cell19_42602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_42602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42602 prefixEnd_42602 := by exact prefixLift 42602
  have htrace : WordTrace (prefixWord ++ tailWord_42602) baseStart_42602 baseEnd_42602 := by
    simpa [prefixWord, tailWord_42602, baseEnd_42602] using wordTrace_append hprefix tailTrace_42602
  have hstable : (prefixWord ++ tailWord_42602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42602).length < 2 ^ (prefixWord ++ tailWord_42602).sum := by decide
  have hdescent : baseEnd_42602 < baseStart_42602 := by decide
  rcases family_descends (prefixWord ++ tailWord_42602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42621 : List Nat := [1, 4, 1, 1, 4, 2, 3, 3]
def baseStart_42621 : Nat := 118140960795 + 42621 * 2 ^ 59
def prefixEnd_42621 : Nat := 4983230072969 + 3 ^ 40 * 42621 * 2
def baseEnd_42621 : Nat := 12968923837263987461627

theorem tailTrace_42621 : CollatzResearch.WordTrace tailWord_42621 prefixEnd_42621 12968923837263987461627 := by
  unfold tailWord_42621
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554515578598870932391717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1036343719065913954927811 1554515578598870932391717)
  ·
    refine ⟨291471670987288299823447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1554515578598870932391717 291471670987288299823447)
    ·
      refine ⟨437207506480932449735171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291471670987288299823447 437207506480932449735171)
      ·
        refine ⟨655811259721398674602757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437207506480932449735171 655811259721398674602757)
        ·
          refine ⟨122964611197762251488017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 655811259721398674602757 122964611197762251488017)
          ·
            refine ⟨92223458398321688616013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122964611197762251488017 92223458398321688616013)
            ·
              refine ⟨34583796899370633231005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92223458398321688616013 34583796899370633231005)
              ·
                refine ⟨12968923837263987461627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34583796899370633231005 12968923837263987461627)
                ·
                  rfl

theorem cell19_42621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_42621 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42621 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42621 prefixEnd_42621 := by exact prefixLift 42621
  have htrace : WordTrace (prefixWord ++ tailWord_42621) baseStart_42621 baseEnd_42621 := by
    simpa [prefixWord, tailWord_42621, baseEnd_42621] using wordTrace_append hprefix tailTrace_42621
  have hstable : (prefixWord ++ tailWord_42621).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42621).length < 2 ^ (prefixWord ++ tailWord_42621).sum := by decide
  have hdescent : baseEnd_42621 < baseStart_42621 := by decide
  rcases family_descends (prefixWord ++ tailWord_42621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42720 : List Nat := [2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_42720 : Nat := 118140960795 + 42720 * 2 ^ 59
def prefixEnd_42720 : Nat := 4983230072969 + 3 ^ 40 * 42720 * 2
def baseEnd_42720 : Nat := 12999048035661091261357

theorem tailTrace_42720 : CollatzResearch.WordTrace tailWord_42720 prefixEnd_42720 12999048035661091261357 := by
  unfold tailWord_42720
  simp only [CollatzResearch.WordTrace]
  refine ⟨779063202620105420122807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1038750936826807226830409 779063202620105420122807)
  ·
    refine ⟨1168594803930158130184211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779063202620105420122807 1168594803930158130184211)
    ·
      refine ⟨1752892205895237195276317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1168594803930158130184211 1752892205895237195276317)
      ·
        refine ⟨657334577210713948228619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1752892205895237195276317 657334577210713948228619)
        ·
          refine ⟨986001865816070922342929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657334577210713948228619 986001865816070922342929)
          ·
            refine ⟨739501399362053191757197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 986001865816070922342929 739501399362053191757197)
            ·
              refine ⟨277313024760769946908949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 739501399362053191757197 277313024760769946908949)
              ·
                refine ⟨12999048035661091261357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 277313024760769946908949 12999048035661091261357)
                ·
                  rfl

theorem cell19_42720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_42720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42720 prefixEnd_42720 := by exact prefixLift 42720
  have htrace : WordTrace (prefixWord ++ tailWord_42720) baseStart_42720 baseEnd_42720 := by
    simpa [prefixWord, tailWord_42720, baseEnd_42720] using wordTrace_append hprefix tailTrace_42720
  have hstable : (prefixWord ++ tailWord_42720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42720).length < 2 ^ (prefixWord ++ tailWord_42720).sum := by decide
  have hdescent : baseEnd_42720 < baseStart_42720 := by decide
  rcases family_descends (prefixWord ++ tailWord_42720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42739 : List Nat := [1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_42739 : Nat := 118140960795 + 42739 * 2 ^ 59
def prefixEnd_42739 : Nat := 4983230072969 + 3 ^ 40 * 42739 * 2
def baseEnd_42739 : Nat := 13004829447474676839083

theorem tailTrace_42739 : CollatzResearch.WordTrace tailWord_42739 prefixEnd_42739 13004829447474676839083 := by
  unfold tailWord_42739
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558819392171377085187271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1039212928114251390124847 1558819392171377085187271)
  ·
    refine ⟨2338229088257065627780907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1558819392171377085187271 2338229088257065627780907)
    ·
      refine ⟨3507343632385598441671361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2338229088257065627780907 3507343632385598441671361)
      ·
        refine ⟨2630507724289198831253521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3507343632385598441671361 2630507724289198831253521)
        ·
          refine ⟨1972880793216899123440141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2630507724289198831253521 1972880793216899123440141)
          ·
            refine ⟨739830297456337171290053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1972880793216899123440141 739830297456337171290053)
            ·
              refine ⟨138718180773063219616885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 739830297456337171290053 138718180773063219616885)
              ·
                refine ⟨13004829447474676839083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138718180773063219616885 13004829447474676839083)
                ·
                  rfl

theorem cell19_42739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_42739 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42739 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42739 prefixEnd_42739 := by exact prefixLift 42739
  have htrace : WordTrace (prefixWord ++ tailWord_42739) baseStart_42739 baseEnd_42739 := by
    simpa [prefixWord, tailWord_42739, baseEnd_42739] using wordTrace_append hprefix tailTrace_42739
  have hstable : (prefixWord ++ tailWord_42739).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42739).length < 2 ^ (prefixWord ++ tailWord_42739).sum := by decide
  have hdescent : baseEnd_42739 < baseStart_42739 := by decide
  rcases family_descends (prefixWord ++ tailWord_42739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42765 : List Nat := [1, 7, 2, 1, 2, 1, 1, 4]
def baseStart_42765 : Nat := 118140960795 + 42765 * 2 ^ 59
def prefixEnd_42765 : Nat := 4983230072969 + 3 ^ 40 * 42765 * 2
def baseEnd_42765 : Nat := 13012740853114320261235

theorem tailTrace_42765 : CollatzResearch.WordTrace tailWord_42765 prefixEnd_42765 13012740853114320261235 := by
  unfold tailWord_42765
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559767690077183525633749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1039845126718122350422499 1559767690077183525633749)
  ·
    refine ⟨36557055236183988882041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1559767690077183525633749 36557055236183988882041)
    ·
      refine ⟨27417791427137991661531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36557055236183988882041 27417791427137991661531)
      ·
        refine ⟨41126687140706987492297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27417791427137991661531 41126687140706987492297)
        ·
          refine ⟨30845015355530240619223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41126687140706987492297 30845015355530240619223)
          ·
            refine ⟨46267523033295360928835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30845015355530240619223 46267523033295360928835)
            ·
              refine ⟨69401284549943041393253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46267523033295360928835 69401284549943041393253)
              ·
                refine ⟨13012740853114320261235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69401284549943041393253 13012740853114320261235)
                ·
                  rfl

theorem cell19_42765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 4].length) (baseStart_42765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42765 prefixEnd_42765 := by exact prefixLift 42765
  have htrace : WordTrace (prefixWord ++ tailWord_42765) baseStart_42765 baseEnd_42765 := by
    simpa [prefixWord, tailWord_42765, baseEnd_42765] using wordTrace_append hprefix tailTrace_42765
  have hstable : (prefixWord ++ tailWord_42765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42765).length < 2 ^ (prefixWord ++ tailWord_42765).sum := by decide
  have hdescent : baseEnd_42765 < baseStart_42765 := by decide
  rcases family_descends (prefixWord ++ tailWord_42765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42775 : List Nat := [1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_42775 : Nat := 118140960795 + 42775 * 2 ^ 59
def prefixEnd_42775 : Nat := 4983230072969 + 3 ^ 40 * 42775 * 2
def baseEnd_42775 : Nat := 13015783701437260038985

theorem tailTrace_42775 : CollatzResearch.WordTrace tailWord_42775 prefixEnd_42775 13015783701437260038985 := by
  unfold tailWord_42775
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560132420040955233497779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1040088280027303488998519 1560132420040955233497779)
  ·
    refine ⟨2340198630061432850246669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1560132420040955233497779 2340198630061432850246669)
    ·
      refine ⟨877574486273037318842501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2340198630061432850246669 877574486273037318842501)
      ·
        refine ⟨164545216176194497282969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 877574486273037318842501 164545216176194497282969)
        ·
          refine ⟨123408912132145872962227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164545216176194497282969 123408912132145872962227)
          ·
            refine ⟨185113368198218809443341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123408912132145872962227 185113368198218809443341)
            ·
              refine ⟨69417513074332053541253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185113368198218809443341 69417513074332053541253)
              ·
                refine ⟨13015783701437260038985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69417513074332053541253 13015783701437260038985)
                ·
                  rfl

theorem cell19_42775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_42775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42775 prefixEnd_42775 := by exact prefixLift 42775
  have htrace : WordTrace (prefixWord ++ tailWord_42775) baseStart_42775 baseEnd_42775 := by
    simpa [prefixWord, tailWord_42775, baseEnd_42775] using wordTrace_append hprefix tailTrace_42775
  have hstable : (prefixWord ++ tailWord_42775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42775).length < 2 ^ (prefixWord ++ tailWord_42775).sum := by decide
  have hdescent : baseEnd_42775 < baseStart_42775 := by decide
  rcases family_descends (prefixWord ++ tailWord_42775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42792 : List Nat := [2, 1, 5, 1, 1, 3, 3, 3]
def baseStart_42792 : Nat := 118140960795 + 42792 * 2 ^ 59
def prefixEnd_42792 : Nat := 4983230072969 + 3 ^ 40 * 42792 * 2
def baseEnd_42792 : Nat := 13020956543586257661161

theorem tailTrace_42792 : CollatzResearch.WordTrace tailWord_42792 prefixEnd_42792 13020956543586257661161 := by
  unfold tailWord_42792
  simp only [CollatzResearch.WordTrace]
  refine ⟨780376230489683568433315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1040501640652911424577753 780376230489683568433315)
  ·
    refine ⟨1170564345734525352649973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 780376230489683568433315 1170564345734525352649973)
    ·
      refine ⟨109740407412611751810935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1170564345734525352649973 109740407412611751810935)
      ·
        refine ⟨164610611118917627716403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109740407412611751810935 164610611118917627716403)
        ·
          refine ⟨246915916678376441574605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164610611118917627716403 246915916678376441574605)
          ·
            refine ⟨92593468754391165590477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246915916678376441574605 92593468754391165590477)
            ·
              refine ⟨34722550782896687096429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92593468754391165590477 34722550782896687096429)
              ·
                refine ⟨13020956543586257661161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34722550782896687096429 13020956543586257661161)
                ·
                  rfl

theorem cell19_42792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_42792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42792 prefixEnd_42792 := by exact prefixLift 42792
  have htrace : WordTrace (prefixWord ++ tailWord_42792) baseStart_42792 baseEnd_42792 := by
    simpa [prefixWord, tailWord_42792, baseEnd_42792] using wordTrace_append hprefix tailTrace_42792
  have hstable : (prefixWord ++ tailWord_42792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42792).length < 2 ^ (prefixWord ++ tailWord_42792).sum := by decide
  have hdescent : baseEnd_42792 < baseStart_42792 := by decide
  rcases family_descends (prefixWord ++ tailWord_42792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42813 : List Nat := [1, 4, 1, 4, 1, 2, 6]
def baseStart_42813 : Nat := 118140960795 + 42813 * 2 ^ 59
def prefixEnd_42813 : Nat := 4983230072969 + 3 ^ 40 * 42813 * 2
def baseEnd_42813 : Nat := 4342448841688143731479

theorem tailTrace_42813 : CollatzResearch.WordTrace tailWord_42813 prefixEnd_42813 4342448841688143731479 := by
  unfold tailWord_42813
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561518393903287723381093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1041012262602191815587395 1561518393903287723381093)
  ·
    refine ⟨292784698856866448133955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1561518393903287723381093 292784698856866448133955)
    ·
      refine ⟨439177048285299672200933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292784698856866448133955 439177048285299672200933)
      ·
        refine ⟨82345696553493688537675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 439177048285299672200933 82345696553493688537675)
        ·
          refine ⟨123518544830240532806513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82345696553493688537675 123518544830240532806513)
          ·
            refine ⟨92638908622680399604885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123518544830240532806513 92638908622680399604885)
            ·
              refine ⟨4342448841688143731479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92638908622680399604885 4342448841688143731479)
              ·
                rfl

theorem cell19_42813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 6].length) (baseStart_42813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42813 prefixEnd_42813 := by exact prefixLift 42813
  have htrace : WordTrace (prefixWord ++ tailWord_42813) baseStart_42813 baseEnd_42813 := by
    simpa [prefixWord, tailWord_42813, baseEnd_42813] using wordTrace_append hprefix tailTrace_42813
  have hstable : (prefixWord ++ tailWord_42813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42813).length < 2 ^ (prefixWord ++ tailWord_42813).sum := by decide
  have hdescent : baseEnd_42813 < baseStart_42813 := by decide
  rcases family_descends (prefixWord ++ tailWord_42813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42851 : List Nat := [1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_42851 : Nat := 118140960795 + 42851 * 2 ^ 59
def prefixEnd_42851 : Nat := 4983230072969 + 3 ^ 40 * 42851 * 2
def baseEnd_42851 : Nat := 13038909348691602349889

theorem tailTrace_42851 : CollatzResearch.WordTrace tailWord_42851 prefixEnd_42851 13038909348691602349889 := by
  unfold tailWord_42851
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562904367765620213264407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1041936245177080142176271 1562904367765620213264407)
  ·
    refine ⟨2344356551648430319896611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1562904367765620213264407 2344356551648430319896611)
    ·
      refine ⟨3516534827472645479844917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2344356551648430319896611 3516534827472645479844917)
      ·
        refine ⟨329675140075560513735461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3516534827472645479844917 329675140075560513735461)
        ·
          refine ⟨61814088764167596325399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329675140075560513735461 61814088764167596325399)
          ·
            refine ⟨92721133146251394488099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61814088764167596325399 92721133146251394488099)
            ·
              refine ⟨139081699719377091732149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92721133146251394488099 139081699719377091732149)
              ·
                refine ⟨13038909348691602349889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139081699719377091732149 13038909348691602349889)
                ·
                  rfl

theorem cell19_42851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_42851 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42851 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42851 prefixEnd_42851 := by exact prefixLift 42851
  have htrace : WordTrace (prefixWord ++ tailWord_42851) baseStart_42851 baseEnd_42851 := by
    simpa [prefixWord, tailWord_42851, baseEnd_42851] using wordTrace_append hprefix tailTrace_42851
  have hstable : (prefixWord ++ tailWord_42851).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42851).length < 2 ^ (prefixWord ++ tailWord_42851).sum := by decide
  have hdescent : baseEnd_42851 < baseStart_42851 := by decide
  rcases family_descends (prefixWord ++ tailWord_42851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42908 : List Nat := [2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_42908 : Nat := 118140960795 + 42908 * 2 ^ 59
def prefixEnd_42908 : Nat := 4983230072969 + 3 ^ 40 * 42908 * 2
def baseEnd_42908 : Nat := 13056253584132359083067

theorem tailTrace_42908 : CollatzResearch.WordTrace tailWord_42908 prefixEnd_42908 13056253584132359083067 := by
  unfold tailWord_42908
  simp only [CollatzResearch.WordTrace]
  refine ⟨782491664279559474044689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1043322219039412632059585 782491664279559474044689)
  ·
    refine ⟨586868748209669605533517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 782491664279559474044689 586868748209669605533517)
    ·
      refine ⟨220075780578626102075069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 586868748209669605533517 220075780578626102075069)
      ·
        refine ⟨82528417716984788278151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220075780578626102075069 82528417716984788278151)
        ·
          refine ⟨123792626575477182417227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82528417716984788278151 123792626575477182417227)
          ·
            refine ⟨185688939863215773625841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123792626575477182417227 185688939863215773625841)
            ·
              refine ⟨139266704897411830219381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185688939863215773625841 139266704897411830219381)
              ·
                refine ⟨13056253584132359083067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139266704897411830219381 13056253584132359083067)
                ·
                  rfl

theorem cell19_42908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_42908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42908 prefixEnd_42908 := by exact prefixLift 42908
  have htrace : WordTrace (prefixWord ++ tailWord_42908) baseStart_42908 baseEnd_42908 := by
    simpa [prefixWord, tailWord_42908, baseEnd_42908] using wordTrace_append hprefix tailTrace_42908
  have hstable : (prefixWord ++ tailWord_42908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42908).length < 2 ^ (prefixWord ++ tailWord_42908).sum := by decide
  have hdescent : baseEnd_42908 < baseStart_42908 := by decide
  rcases family_descends (prefixWord ++ tailWord_42908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42929 : List Nat := [1, 2, 2, 4, 2, 8]
def baseStart_42929 : Nat := 118140960795 + 42929 * 2 ^ 59
def prefixEnd_42929 : Nat := 4983230072969 + 3 ^ 40 * 42929 * 2
def baseEnd_42929 : Nat := 1451404840623392512927

theorem tailTrace_42929 : CollatzResearch.WordTrace tailWord_42929 prefixEnd_42929 1451404840623392512927 := by
  unfold tailWord_42929
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565749261483039534603841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1043832840988693023069227 1565749261483039534603841)
  ·
    refine ⟨1174311946112279650952881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1565749261483039534603841 1174311946112279650952881)
    ·
      refine ⟨880733959584209738214661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1174311946112279650952881 880733959584209738214661)
      ·
        refine ⟨165137617422039325915249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 880733959584209738214661 165137617422039325915249)
        ·
          refine ⟨123853213066529494436437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165137617422039325915249 123853213066529494436437)
          ·
            refine ⟨1451404840623392512927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 123853213066529494436437 1451404840623392512927)
            ·
              rfl

theorem cell19_42929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 8].length) (baseStart_42929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42929 prefixEnd_42929 := by exact prefixLift 42929
  have htrace : WordTrace (prefixWord ++ tailWord_42929) baseStart_42929 baseEnd_42929 := by
    simpa [prefixWord, tailWord_42929, baseEnd_42929] using wordTrace_append hprefix tailTrace_42929
  have hstable : (prefixWord ++ tailWord_42929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42929).length < 2 ^ (prefixWord ++ tailWord_42929).sum := by decide
  have hdescent : baseEnd_42929 < baseStart_42929 := by decide
  rcases family_descends (prefixWord ++ tailWord_42929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42986 : List Nat := [3, 1, 3, 1, 2, 1, 8]
def baseStart_42986 : Nat := 118140960795 + 42986 * 2 ^ 59
def prefixEnd_42986 : Nat := 4983230072969 + 3 ^ 40 * 42986 * 2
def baseEnd_42986 : Nat := 4359995933683763116507

theorem tailTrace_42986 : CollatzResearch.WordTrace tailWord_42986 prefixEnd_42986 4359995933683763116507 := by
  unfold tailWord_42986
  simp only [CollatzResearch.WordTrace]
  refine ⟨391957055569134567357203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1045218814851025512952541 391957055569134567357203)
  ·
    refine ⟨587935583353701851035805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391957055569134567357203 587935583353701851035805)
    ·
      refine ⟨220475843757638194138427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 587935583353701851035805 220475843757638194138427)
      ·
        refine ⟨330713765636457291207641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220475843757638194138427 330713765636457291207641)
        ·
          refine ⟨248035324227342968405731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330713765636457291207641 248035324227342968405731)
          ·
            refine ⟨372052986341014452608597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248035324227342968405731 372052986341014452608597)
            ·
              refine ⟨4359995933683763116507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 372052986341014452608597 4359995933683763116507)
              ·
                rfl

theorem cell19_42986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_42986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_42986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_42986 prefixEnd_42986 := by exact prefixLift 42986
  have htrace : WordTrace (prefixWord ++ tailWord_42986) baseStart_42986 baseEnd_42986 := by
    simpa [prefixWord, tailWord_42986, baseEnd_42986] using wordTrace_append hprefix tailTrace_42986
  have hstable : (prefixWord ++ tailWord_42986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42986).length < 2 ^ (prefixWord ++ tailWord_42986).sum := by decide
  have hdescent : baseEnd_42986 < baseStart_42986 := by decide
  rcases family_descends (prefixWord ++ tailWord_42986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43018 : List Nat := [3, 1, 2, 2, 5, 1, 2, 3]
def baseStart_43018 : Nat := 118140960795 + 43018 * 2 ^ 59
def prefixEnd_43018 : Nat := 4983230072969 + 3 ^ 40 * 43018 * 2
def baseEnd_43018 : Nat := 13089724915684696638323

theorem tailTrace_43018 : CollatzResearch.WordTrace tailWord_43018 prefixEnd_43018 13089724915684696638323 := by
  unfold tailWord_43018
  simp only [CollatzResearch.WordTrace]
  refine ⟨392248839540151933648427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1045996905440405156395805 392248839540151933648427)
  ·
    refine ⟨588373259310227900472641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 392248839540151933648427 588373259310227900472641)
    ·
      refine ⟨441279944482670925354481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 588373259310227900472641 441279944482670925354481)
      ·
        refine ⟨330959958362003194015861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441279944482670925354481 330959958362003194015861)
        ·
          refine ⟨31027496096437799438987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 330959958362003194015861 31027496096437799438987)
          ·
            refine ⟨46541244144656699158481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31027496096437799438987 46541244144656699158481)
            ·
              refine ⟨34905933108492524368861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46541244144656699158481 34905933108492524368861)
              ·
                refine ⟨13089724915684696638323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34905933108492524368861 13089724915684696638323)
                ·
                  rfl

theorem cell19_43018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_43018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43018 prefixEnd_43018 := by exact prefixLift 43018
  have htrace : WordTrace (prefixWord ++ tailWord_43018) baseStart_43018 baseEnd_43018 := by
    simpa [prefixWord, tailWord_43018, baseEnd_43018] using wordTrace_append hprefix tailTrace_43018
  have hstable : (prefixWord ++ tailWord_43018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43018).length < 2 ^ (prefixWord ++ tailWord_43018).sum := by decide
  have hdescent : baseEnd_43018 < baseStart_43018 := by decide
  rcases family_descends (prefixWord ++ tailWord_43018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43041 : List Nat := [1, 2, 3, 2, 4, 2, 5]
def baseStart_43041 : Nat := 118140960795 + 43041 * 2 ^ 59
def prefixEnd_43041 : Nat := 4983230072969 + 3 ^ 40 * 43041 * 2
def baseEnd_43041 : Nat := 4365574488942486042383

theorem tailTrace_43041 : CollatzResearch.WordTrace tailWord_43041 prefixEnd_43041 4365574488942486042383 := by
  unfold tailWord_43041
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569834237077282662680977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1046556158051521775120651 1569834237077282662680977)
  ·
    refine ⟨1177375677807961997010733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1569834237077282662680977 1177375677807961997010733)
    ·
      refine ⟨441515879177985748879025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1177375677807961997010733 441515879177985748879025)
      ·
        refine ⟨331136909383489311659269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441515879177985748879025 331136909383489311659269)
        ·
          refine ⟨62088170509404245936113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331136909383489311659269 62088170509404245936113)
          ·
            refine ⟨46566127882053184452085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62088170509404245936113 46566127882053184452085)
            ·
              refine ⟨4365574488942486042383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46566127882053184452085 4365574488942486042383)
              ·
                rfl

theorem cell19_43041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_43041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43041 prefixEnd_43041 := by exact prefixLift 43041
  have htrace : WordTrace (prefixWord ++ tailWord_43041) baseStart_43041 baseEnd_43041 := by
    simpa [prefixWord, tailWord_43041, baseEnd_43041] using wordTrace_append hprefix tailTrace_43041
  have hstable : (prefixWord ++ tailWord_43041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43041).length < 2 ^ (prefixWord ++ tailWord_43041).sum := by decide
  have hdescent : baseEnd_43041 < baseStart_43041 := by decide
  rcases family_descends (prefixWord ++ tailWord_43041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43100 : List Nat := [2, 2, 4, 1, 1, 9]
def baseStart_43100 : Nat := 118140960795 + 43100 * 2 ^ 59
def prefixEnd_43100 : Nat := 4983230072969 + 3 ^ 40 * 43100 * 2
def baseEnd_43100 : Nat := 1457186252436978090653

theorem tailTrace_43100 : CollatzResearch.WordTrace tailWord_43100 prefixEnd_43100 1457186252436978090653 := by
  unfold tailWord_43100
  simp only [CollatzResearch.WordTrace]
  refine ⟨785993071931767869539377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1047990762575690492719169 785993071931767869539377)
  ·
    refine ⟨589494803948825902154533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 785993071931767869539377 589494803948825902154533)
    ·
      refine ⟨110530275740404856653975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 589494803948825902154533 110530275740404856653975)
      ·
        refine ⟨165795413610607284980963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110530275740404856653975 165795413610607284980963)
        ·
          refine ⟨248693120415910927471445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165795413610607284980963 248693120415910927471445)
          ·
            refine ⟨1457186252436978090653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 248693120415910927471445 1457186252436978090653)
            ·
              rfl

theorem cell19_43100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 9].length) (baseStart_43100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43100 prefixEnd_43100 := by exact prefixLift 43100
  have htrace : WordTrace (prefixWord ++ tailWord_43100) baseStart_43100 baseEnd_43100 := by
    simpa [prefixWord, tailWord_43100, baseEnd_43100] using wordTrace_append hprefix tailTrace_43100
  have hstable : (prefixWord ++ tailWord_43100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43100).length < 2 ^ (prefixWord ++ tailWord_43100).sum := by decide
  have hdescent : baseEnd_43100 < baseStart_43100 := by decide
  rcases family_descends (prefixWord ++ tailWord_43100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43119 : List Nat := [1, 1, 2, 1, 3, 4, 3, 4]
def baseStart_43119 : Nat := 118140960795 + 43119 * 2 ^ 59
def prefixEnd_43119 : Nat := 4983230072969 + 3 ^ 40 * 43119 * 2
def baseEnd_43119 : Nat := 13120457683746388393603

theorem tailTrace_43119 : CollatzResearch.WordTrace tailWord_43119 prefixEnd_43119 13120457683746388393603 := by
  unfold tailWord_43119
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572679130794701984020411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1048452753863134656013607 1572679130794701984020411)
  ·
    refine ⟨2359018696192052976030617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1572679130794701984020411 2359018696192052976030617)
    ·
      refine ⟨1769264022144039732022963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2359018696192052976030617 1769264022144039732022963)
      ·
        refine ⟨2653896033216059598034445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769264022144039732022963 2653896033216059598034445)
        ·
          refine ⟨995211012456022349262917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2653896033216059598034445 995211012456022349262917)
          ·
            refine ⟨186602064835504190486797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 995211012456022349262917 186602064835504190486797)
            ·
              refine ⟨69975774313314071432549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186602064835504190486797 69975774313314071432549)
              ·
                refine ⟨13120457683746388393603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69975774313314071432549 13120457683746388393603)
                ·
                  rfl

theorem cell19_43119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_43119 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43119 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43119 prefixEnd_43119 := by exact prefixLift 43119
  have htrace : WordTrace (prefixWord ++ tailWord_43119) baseStart_43119 baseEnd_43119 := by
    simpa [prefixWord, tailWord_43119, baseEnd_43119] using wordTrace_append hprefix tailTrace_43119
  have hstable : (prefixWord ++ tailWord_43119).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43119).length < 2 ^ (prefixWord ++ tailWord_43119).sum := by decide
  have hdescent : baseEnd_43119 < baseStart_43119 := by decide
  rcases family_descends (prefixWord ++ tailWord_43119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43189 : List Nat := [1, 3, 3, 4, 1, 2, 2, 3]
def baseStart_43189 : Nat := 118140960795 + 43189 * 2 ^ 59
def prefixEnd_43189 : Nat := 4983230072969 + 3 ^ 40 * 43189 * 2
def baseEnd_43189 : Nat := 13141757622006966837857

theorem tailTrace_43189 : CollatzResearch.WordTrace tailWord_43189 prefixEnd_43189 13141757622006966837857 := by
  unfold tailWord_43189
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575232240541103939068621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1050154827027402626045747 1575232240541103939068621)
  ·
    refine ⟨590712090202913977150733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1575232240541103939068621 590712090202913977150733)
    ·
      refine ⟨221517033826092741431525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 590712090202913977150733 221517033826092741431525)
      ·
        refine ⟨41534443842392389018411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221517033826092741431525 41534443842392389018411)
        ·
          refine ⟨62301665763588583527617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41534443842392389018411 62301665763588583527617)
          ·
            refine ⟨46726249322691437645713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62301665763588583527617 46726249322691437645713)
            ·
              refine ⟨35044686992018578234285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46726249322691437645713 35044686992018578234285)
              ·
                refine ⟨13141757622006966837857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35044686992018578234285 13141757622006966837857)
                ·
                  rfl

theorem cell19_43189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_43189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43189 prefixEnd_43189 := by exact prefixLift 43189
  have htrace : WordTrace (prefixWord ++ tailWord_43189) baseStart_43189 baseEnd_43189 := by
    simpa [prefixWord, tailWord_43189, baseEnd_43189] using wordTrace_append hprefix tailTrace_43189
  have hstable : (prefixWord ++ tailWord_43189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43189).length < 2 ^ (prefixWord ++ tailWord_43189).sum := by decide
  have hdescent : baseEnd_43189 < baseStart_43189 := by decide
  rcases family_descends (prefixWord ++ tailWord_43189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43214 : List Nat := [4, 1, 1, 1, 4, 1, 7]
def baseStart_43214 : Nat := 118140960795 + 43214 * 2 ^ 59
def prefixEnd_43214 : Nat := 4983230072969 + 3 ^ 40 * 43214 * 2
def baseEnd_43214 : Nat := 4383121580938105427411

theorem tailTrace_43214 : CollatzResearch.WordTrace tailWord_43214 prefixEnd_43214 4383121580938105427411 := by
  unfold tailWord_43214
  simp only [CollatzResearch.WordTrace]
  refine ⟨197018008181316651091087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1050762710300355472485797 197018008181316651091087)
  ·
    refine ⟨295527012271974976636631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197018008181316651091087 295527012271974976636631)
    ·
      refine ⟨443290518407962464954947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295527012271974976636631 443290518407962464954947)
      ·
        refine ⟨664935777611943697432421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443290518407962464954947 664935777611943697432421)
        ·
          refine ⟨124675458302239443268579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 664935777611943697432421 124675458302239443268579)
          ·
            refine ⟨187013187453359164902869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124675458302239443268579 187013187453359164902869)
            ·
              refine ⟨4383121580938105427411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 187013187453359164902869 4383121580938105427411)
              ·
                rfl

theorem cell19_43214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_43214 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43214 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43214 prefixEnd_43214 := by exact prefixLift 43214
  have htrace : WordTrace (prefixWord ++ tailWord_43214) baseStart_43214 baseEnd_43214 := by
    simpa [prefixWord, tailWord_43214, baseEnd_43214] using wordTrace_append hprefix tailTrace_43214
  have hstable : (prefixWord ++ tailWord_43214).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43214).length < 2 ^ (prefixWord ++ tailWord_43214).sum := by decide
  have hdescent : baseEnd_43214 < baseStart_43214 := by decide
  rcases family_descends (prefixWord ++ tailWord_43214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43233 : List Nat := [1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_43233 : Nat := 118140960795 + 43233 * 2 ^ 59
def prefixEnd_43233 : Nat := 4983230072969 + 3 ^ 40 * 43233 * 2
def baseEnd_43233 : Nat := 13155146154627901859959

theorem tailTrace_43233 : CollatzResearch.WordTrace tailWord_43233 prefixEnd_43233 13155146154627901859959 := by
  unfold tailWord_43233
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576837052381699453670353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1051224701587799635780235 1576837052381699453670353)
  ·
    refine ⟨1182627789286274590252765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1576837052381699453670353 1182627789286274590252765)
    ·
      refine ⟨443485420982352971344787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1182627789286274590252765 443485420982352971344787)
      ·
        refine ⟨665228131473529457017181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443485420982352971344787 665228131473529457017181)
        ·
          refine ⟨249460549302573546381443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 665228131473529457017181 249460549302573546381443)
          ·
            refine ⟨374190823953860319572165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249460549302573546381443 374190823953860319572165)
            ·
              refine ⟨70160779491348809919781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 374190823953860319572165 70160779491348809919781)
              ·
                refine ⟨13155146154627901859959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70160779491348809919781 13155146154627901859959)
                ·
                  rfl

theorem cell19_43233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_43233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43233 prefixEnd_43233 := by exact prefixLift 43233
  have htrace : WordTrace (prefixWord ++ tailWord_43233) baseStart_43233 baseEnd_43233 := by
    simpa [prefixWord, tailWord_43233, baseEnd_43233] using wordTrace_append hprefix tailTrace_43233
  have hstable : (prefixWord ++ tailWord_43233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43233).length < 2 ^ (prefixWord ++ tailWord_43233).sum := by decide
  have hdescent : baseEnd_43233 < baseStart_43233 := by decide
  rcases family_descends (prefixWord ++ tailWord_43233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43271 : List Nat := [1, 1, 4, 5, 8]
def baseStart_43271 : Nat := 118140960795 + 43271 * 2 ^ 59
def prefixEnd_43271 : Nat := 4983230072969 + 3 ^ 40 * 43271 * 2
def baseEnd_43271 : Nat := 487655888083521222793

theorem tailTrace_43271 : CollatzResearch.WordTrace tailWord_43271 prefixEnd_43271 487655888083521222793 := by
  unfold tailWord_43271
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578223026244031943553667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1052148684162687962369111 1578223026244031943553667)
  ·
    refine ⟨2367334539366047915330501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1578223026244031943553667 2367334539366047915330501)
    ·
      refine ⟨443875226131133984124469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2367334539366047915330501 443875226131133984124469)
      ·
        refine ⟨41613302449793811011669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 443875226131133984124469 41613302449793811011669)
        ·
          refine ⟨487655888083521222793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 41613302449793811011669 487655888083521222793)
          ·
            rfl

theorem cell19_43271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 8].length) (baseStart_43271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43271 prefixEnd_43271 := by exact prefixLift 43271
  have htrace : WordTrace (prefixWord ++ tailWord_43271) baseStart_43271 baseEnd_43271 := by
    simpa [prefixWord, tailWord_43271, baseEnd_43271] using wordTrace_append hprefix tailTrace_43271
  have hstable : (prefixWord ++ tailWord_43271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43271).length < 2 ^ (prefixWord ++ tailWord_43271).sum := by decide
  have hdescent : baseEnd_43271 < baseStart_43271 := by decide
  rcases family_descends (prefixWord ++ tailWord_43271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43273 : List Nat := [1, 2, 1, 1, 3, 11]
def baseStart_43273 : Nat := 118140960795 + 43273 * 2 ^ 59
def prefixEnd_43273 : Nat := 4983230072969 + 3 ^ 40 * 43273 * 2
def baseEnd_43273 : Nat := 1463035283102184552329

theorem tailTrace_43273 : CollatzResearch.WordTrace tailWord_43273 prefixEnd_43273 1463035283102184552329 := by
  unfold tailWord_43273
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578295972236786285126473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1052197314824524190084315 1578295972236786285126473)
  ·
    refine ⟨1183721979177589713844855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1578295972236786285126473 1183721979177589713844855)
    ·
      refine ⟨1775582968766384570767283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1183721979177589713844855 1775582968766384570767283)
      ·
        refine ⟨2663374453149576856150925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775582968766384570767283 2663374453149576856150925)
        ·
          refine ⟨998765419931091321056597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2663374453149576856150925 998765419931091321056597)
          ·
            refine ⟨1463035283102184552329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 998765419931091321056597 1463035283102184552329)
            ·
              rfl

theorem cell19_43273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 11].length) (baseStart_43273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43273 prefixEnd_43273 := by exact prefixLift 43273
  have htrace : WordTrace (prefixWord ++ tailWord_43273) baseStart_43273 baseEnd_43273 := by
    simpa [prefixWord, tailWord_43273, baseEnd_43273] using wordTrace_append hprefix tailTrace_43273
  have hstable : (prefixWord ++ tailWord_43273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43273).length < 2 ^ (prefixWord ++ tailWord_43273).sum := by decide
  have hdescent : baseEnd_43273 < baseStart_43273 := by decide
  rcases family_descends (prefixWord ++ tailWord_43273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43311 : List Nat := [1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_43311 : Nat := 118140960795 + 43311 * 2 ^ 59
def prefixEnd_43311 : Nat := 4983230072969 + 3 ^ 40 * 43311 * 2
def baseEnd_43311 : Nat := 13178880371546832126413

theorem tailTrace_43311 : CollatzResearch.WordTrace tailWord_43311 prefixEnd_43311 13178880371546832126413 := by
  unfold tailWord_43311
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579681946099118775009787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1053121297399412516673191 1579681946099118775009787)
  ·
    refine ⟨2369522919148678162514681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1579681946099118775009787 2369522919148678162514681)
    ·
      refine ⟨1777142189361508621886011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2369522919148678162514681 1777142189361508621886011)
      ·
        refine ⟨2665713284042262932829017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1777142189361508621886011 2665713284042262932829017)
        ·
          refine ⟨1999284963031697199621763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2665713284042262932829017 1999284963031697199621763)
          ·
            refine ⟨2998927444547545799432645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999284963031697199621763 2998927444547545799432645)
            ·
              refine ⟨562298895852664837393621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2998927444547545799432645 562298895852664837393621)
              ·
                refine ⟨13178880371546832126413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 562298895852664837393621 13178880371546832126413)
                ·
                  rfl

theorem cell19_43311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_43311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43311 prefixEnd_43311 := by exact prefixLift 43311
  have htrace : WordTrace (prefixWord ++ tailWord_43311) baseStart_43311 baseEnd_43311 := by
    simpa [prefixWord, tailWord_43311, baseEnd_43311] using wordTrace_append hprefix tailTrace_43311
  have hstable : (prefixWord ++ tailWord_43311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43311).length < 2 ^ (prefixWord ++ tailWord_43311).sum := by decide
  have hdescent : baseEnd_43311 < baseStart_43311 := by decide
  rcases family_descends (prefixWord ++ tailWord_43311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43358 : List Nat := [4, 4, 2, 1, 1, 1, 1, 5]
def baseStart_43358 : Nat := 118140960795 + 43358 * 2 ^ 59
def prefixEnd_43358 : Nat := 4983230072969 + 3 ^ 40 * 43358 * 2
def baseEnd_43358 : Nat := 13193181758664649081841

theorem tailTrace_43358 : CollatzResearch.WordTrace tailWord_43358 prefixEnd_43358 13193181758664649081841 := by
  unfold tailWord_43358
  simp only [CollatzResearch.WordTrace]
  refine ⟨197674522116105725246341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1054264117952563867980485 197674522116105725246341)
  ·
    refine ⟨37063972896769823483689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197674522116105725246341 37063972896769823483689)
    ·
      refine ⟨27797979672577367612767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37063972896769823483689 27797979672577367612767)
      ·
        refine ⟨41696969508866051419151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27797979672577367612767 41696969508866051419151)
        ·
          refine ⟨62545454263299077128727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41696969508866051419151 62545454263299077128727)
          ·
            refine ⟨93818181394948615693091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62545454263299077128727 93818181394948615693091)
            ·
              refine ⟨140727272092422923539637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93818181394948615693091 140727272092422923539637)
              ·
                refine ⟨13193181758664649081841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140727272092422923539637 13193181758664649081841)
                ·
                  rfl

theorem cell19_43358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_43358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43358 prefixEnd_43358 := by exact prefixLift 43358
  have htrace : WordTrace (prefixWord ++ tailWord_43358) baseStart_43358 baseEnd_43358 := by
    simpa [prefixWord, tailWord_43358, baseEnd_43358] using wordTrace_append hprefix tailTrace_43358
  have hstable : (prefixWord ++ tailWord_43358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43358).length < 2 ^ (prefixWord ++ tailWord_43358).sum := by decide
  have hdescent : baseEnd_43358 < baseStart_43358 := by decide
  rcases family_descends (prefixWord ++ tailWord_43358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43362 : List Nat := [3, 3, 2, 1, 1, 4, 2, 3]
def baseStart_43362 : Nat := 118140960795 + 43362 * 2 ^ 59
def prefixEnd_43362 : Nat := 4983230072969 + 3 ^ 40 * 43362 * 2
def baseEnd_43362 : Nat := 13194398897993824992941

theorem tailTrace_43362 : CollatzResearch.WordTrace tailWord_43362 prefixEnd_43362 13194398897993824992941 := by
  unfold tailWord_43362
  simp only [CollatzResearch.WordTrace]
  refine ⟨395385517228588621279085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1054361379276236323410893 395385517228588621279085)
  ·
    refine ⟨148269568960720732979657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 395385517228588621279085 148269568960720732979657)
    ·
      refine ⟨111202176720540549734743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148269568960720732979657 111202176720540549734743)
      ·
        refine ⟨166803265080810824602115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111202176720540549734743 166803265080810824602115)
        ·
          refine ⟨250204897621216236903173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166803265080810824602115 250204897621216236903173)
          ·
            refine ⟨46913418303978044419345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250204897621216236903173 46913418303978044419345)
            ·
              refine ⟨35185063727983533314509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46913418303978044419345 35185063727983533314509)
              ·
                refine ⟨13194398897993824992941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35185063727983533314509 13194398897993824992941)
                ·
                  rfl

theorem cell19_43362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_43362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43362 prefixEnd_43362 := by exact prefixLift 43362
  have htrace : WordTrace (prefixWord ++ tailWord_43362) baseStart_43362 baseEnd_43362 := by
    simpa [prefixWord, tailWord_43362, baseEnd_43362] using wordTrace_append hprefix tailTrace_43362
  have hstable : (prefixWord ++ tailWord_43362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43362).length < 2 ^ (prefixWord ++ tailWord_43362).sum := by decide
  have hdescent : baseEnd_43362 < baseStart_43362 := by decide
  rcases family_descends (prefixWord ++ tailWord_43362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43387 : List Nat := [1, 1, 1, 1, 1, 7, 7]
def baseStart_43387 : Nat := 118140960795 + 43387 * 2 ^ 59
def prefixEnd_43387 : Nat := 4983230072969 + 3 ^ 40 * 43387 * 2
def baseEnd_43387 : Nat := 4400668672933724812439

theorem tailTrace_43387 : CollatzResearch.WordTrace tailWord_43387 prefixEnd_43387 4400668672933724812439 := by
  unfold tailWord_43387
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582453893823783754776415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1054969262549189169850943 1582453893823783754776415)
  ·
    refine ⟨2373680840735675632164623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582453893823783754776415 2373680840735675632164623)
    ·
      refine ⟨3560521261103513448246935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2373680840735675632164623 3560521261103513448246935)
      ·
        refine ⟨5340781891655270172370403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560521261103513448246935 5340781891655270172370403)
        ·
          refine ⟨8011172837482905258555605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340781891655270172370403 8011172837482905258555605)
          ·
            refine ⟨187761863378505591997397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8011172837482905258555605 187761863378505591997397)
            ·
              refine ⟨4400668672933724812439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 187761863378505591997397 4400668672933724812439)
              ·
                rfl

theorem cell19_43387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_43387 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43387 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43387 prefixEnd_43387 := by exact prefixLift 43387
  have htrace : WordTrace (prefixWord ++ tailWord_43387) baseStart_43387 baseEnd_43387 := by
    simpa [prefixWord, tailWord_43387, baseEnd_43387] using wordTrace_append hprefix tailTrace_43387
  have hstable : (prefixWord ++ tailWord_43387).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43387).length < 2 ^ (prefixWord ++ tailWord_43387).sum := by decide
  have hdescent : baseEnd_43387 < baseStart_43387 := by decide
  rcases family_descends (prefixWord ++ tailWord_43387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43404 : List Nat := [2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_43404 : Nat := 118140960795 + 43404 * 2 ^ 59
def prefixEnd_43404 : Nat := 4983230072969 + 3 ^ 40 * 43404 * 2
def baseEnd_43404 : Nat := 13207178860950172059493

theorem tailTrace_43404 : CollatzResearch.WordTrace tailWord_43404 prefixEnd_43404 13207178860950172059493 := by
  unfold tailWord_43404
  simp only [CollatzResearch.WordTrace]
  refine ⟨791536967381097829072633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1055382623174797105430177 791536967381097829072633)
  ·
    refine ⟨593652725535823371804475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 791536967381097829072633 593652725535823371804475)
    ·
      refine ⟨890479088303735057706713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593652725535823371804475 890479088303735057706713)
      ·
        refine ⟨667859316227801293280035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 890479088303735057706713 667859316227801293280035)
        ·
          refine ⟨1001788974341701939920053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667859316227801293280035 1001788974341701939920053)
          ·
            refine ⟨93917716344534556867505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1001788974341701939920053 93917716344534556867505)
            ·
              refine ⟨70438287258400917650629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93917716344534556867505 70438287258400917650629)
              ·
                refine ⟨13207178860950172059493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70438287258400917650629 13207178860950172059493)
                ·
                  rfl

theorem cell19_43404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_43404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43404 prefixEnd_43404 := by exact prefixLift 43404
  have htrace : WordTrace (prefixWord ++ tailWord_43404) baseStart_43404 baseEnd_43404 := by
    simpa [prefixWord, tailWord_43404, baseEnd_43404] using wordTrace_append hprefix tailTrace_43404
  have hstable : (prefixWord ++ tailWord_43404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43404).length < 2 ^ (prefixWord ++ tailWord_43404).sum := by decide
  have hdescent : baseEnd_43404 < baseStart_43404 := by decide
  rcases family_descends (prefixWord ++ tailWord_43404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43533 : List Nat := [1, 7, 1, 1, 1, 2, 1, 5]
def baseStart_43533 : Nat := 118140960795 + 43533 * 2 ^ 59
def prefixEnd_43533 : Nat := 4983230072969 + 3 ^ 40 * 43533 * 2
def baseEnd_43533 : Nat := 13246431604316095192475

theorem tailTrace_43533 : CollatzResearch.WordTrace tailWord_43533 prefixEnd_43533 13246431604316095192475 := by
  unfold tailWord_43533
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587778951294850689591253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1058519300863233793060835 1587778951294850689591253)
  ·
    refine ⟨37213569170973063037295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1587778951294850689591253 37213569170973063037295)
    ·
      refine ⟨55820353756459594555943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37213569170973063037295 55820353756459594555943)
      ·
        refine ⟨83730530634689391833915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55820353756459594555943 83730530634689391833915)
        ·
          refine ⟨125595795952034087750873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83730530634689391833915 125595795952034087750873)
          ·
            refine ⟨94196846964025565813155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125595795952034087750873 94196846964025565813155)
            ·
              refine ⟨141295270446038348719733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94196846964025565813155 141295270446038348719733)
              ·
                refine ⟨13246431604316095192475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141295270446038348719733 13246431604316095192475)
                ·
                  rfl

theorem cell19_43533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_43533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43533 prefixEnd_43533 := by exact prefixLift 43533
  have htrace : WordTrace (prefixWord ++ tailWord_43533) baseStart_43533 baseEnd_43533 := by
    simpa [prefixWord, tailWord_43533, baseEnd_43533] using wordTrace_append hprefix tailTrace_43533
  have hstable : (prefixWord ++ tailWord_43533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43533).length < 2 ^ (prefixWord ++ tailWord_43533).sum := by decide
  have hdescent : baseEnd_43533 < baseStart_43533 := by decide
  rcases family_descends (prefixWord ++ tailWord_43533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43539 : List Nat := [1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_43539 : Nat := 118140960795 + 43539 * 2 ^ 59
def prefixEnd_43539 : Nat := 4983230072969 + 3 ^ 40 * 43539 * 2
def baseEnd_43539 : Nat := 13248257313309859059125

theorem tailTrace_43539 : CollatzResearch.WordTrace tailWord_43539 prefixEnd_43539 13248257313309859059125 := by
  unfold tailWord_43539
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587997789273113714309671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1058665192848742476206447 1587997789273113714309671)
  ·
    refine ⟨2381996683909670571464507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587997789273113714309671 2381996683909670571464507)
    ·
      refine ⟨3572995025864505857196761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381996683909670571464507 3572995025864505857196761)
      ·
        refine ⟨2679746269398379392897571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3572995025864505857196761 2679746269398379392897571)
        ·
          refine ⟨4019619404097569089346357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2679746269398379392897571 4019619404097569089346357)
          ·
            refine ⟨376839319134147102126221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4019619404097569089346357 376839319134147102126221)
            ·
              refine ⟨141314744675305163297333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376839319134147102126221 141314744675305163297333)
              ·
                refine ⟨13248257313309859059125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141314744675305163297333 13248257313309859059125)
                ·
                  rfl

theorem cell19_43539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_43539 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43539 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43539 prefixEnd_43539 := by exact prefixLift 43539
  have htrace : WordTrace (prefixWord ++ tailWord_43539) baseStart_43539 baseEnd_43539 := by
    simpa [prefixWord, tailWord_43539, baseEnd_43539] using wordTrace_append hprefix tailTrace_43539
  have hstable : (prefixWord ++ tailWord_43539).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43539).length < 2 ^ (prefixWord ++ tailWord_43539).sum := by decide
  have hdescent : baseEnd_43539 < baseStart_43539 := by decide
  rcases family_descends (prefixWord ++ tailWord_43539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43596 : List Nat := [2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_43596 : Nat := 118140960795 + 43596 * 2 ^ 59
def prefixEnd_43596 : Nat := 4983230072969 + 3 ^ 40 * 43596 * 2
def baseEnd_43596 : Nat := 13265601548750615792303

theorem tailTrace_43596 : CollatzResearch.WordTrace tailWord_43596 prefixEnd_43596 13265601548750615792303 := by
  unfold tailWord_43596
  simp only [CollatzResearch.WordTrace]
  refine ⟨795038375033306224567321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1060051166711074966089761 795038375033306224567321)
  ·
    refine ⟨596278781274979668425491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 795038375033306224567321 596278781274979668425491)
    ·
      refine ⟨894418171912469502638237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596278781274979668425491 894418171912469502638237)
      ·
        refine ⟨335406814467176063489339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 894418171912469502638237 335406814467176063489339)
        ·
          refine ⟨503110221700764095234009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335406814467176063489339 503110221700764095234009)
          ·
            refine ⟨377332666275573071425507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503110221700764095234009 377332666275573071425507)
            ·
              refine ⟨565998999413359607138261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377332666275573071425507 565998999413359607138261)
              ·
                refine ⟨13265601548750615792303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 565998999413359607138261 13265601548750615792303)
                ·
                  rfl

theorem cell19_43596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_43596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43596 prefixEnd_43596 := by exact prefixLift 43596
  have htrace : WordTrace (prefixWord ++ tailWord_43596) baseStart_43596 baseEnd_43596 := by
    simpa [prefixWord, tailWord_43596, baseEnd_43596] using wordTrace_append hprefix tailTrace_43596
  have hstable : (prefixWord ++ tailWord_43596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43596).length < 2 ^ (prefixWord ++ tailWord_43596).sum := by decide
  have hdescent : baseEnd_43596 < baseStart_43596 := by decide
  rcases family_descends (prefixWord ++ tailWord_43596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43630 : List Nat := [4, 1, 2, 2, 2, 3, 1, 4]
def baseStart_43630 : Nat := 118140960795 + 43630 * 2 ^ 59
def prefixEnd_43630 : Nat := 4983230072969 + 3 ^ 40 * 43630 * 2
def baseEnd_43630 : Nat := 13275947233048611036655

theorem tailTrace_43630 : CollatzResearch.WordTrace tailWord_43630 prefixEnd_43630 13275947233048611036655 := by
  unfold tailWord_43630
  simp only [CollatzResearch.WordTrace]
  refine ⟨198914603992929531984043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1060877887962290837248229 198914603992929531984043)
  ·
    refine ⟨298371905989394297976065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198914603992929531984043 298371905989394297976065)
    ·
      refine ⟨223778929492045723482049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298371905989394297976065 223778929492045723482049)
      ·
        refine ⟨167834197119034292611537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223778929492045723482049 167834197119034292611537)
        ·
          refine ⟨125875647839275719458653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167834197119034292611537 125875647839275719458653)
          ·
            refine ⟨47203367939728394796995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125875647839275719458653 47203367939728394796995)
            ·
              refine ⟨70805051909592592195493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47203367939728394796995 70805051909592592195493)
              ·
                refine ⟨13275947233048611036655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70805051909592592195493 13275947233048611036655)
                ·
                  rfl

theorem cell19_43630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_43630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43630 prefixEnd_43630 := by exact prefixLift 43630
  have htrace : WordTrace (prefixWord ++ tailWord_43630) baseStart_43630 baseEnd_43630 := by
    simpa [prefixWord, tailWord_43630, baseEnd_43630] using wordTrace_append hprefix tailTrace_43630
  have hstable : (prefixWord ++ tailWord_43630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43630).length < 2 ^ (prefixWord ++ tailWord_43630).sum := by decide
  have hdescent : baseEnd_43630 < baseStart_43630 := by decide
  rcases family_descends (prefixWord ++ tailWord_43630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43672 : List Nat := [2, 1, 2, 4, 1, 1, 8]
def baseStart_43672 : Nat := 118140960795 + 43672 * 2 ^ 59
def prefixEnd_43672 : Nat := 4983230072969 + 3 ^ 40 * 43672 * 2
def baseEnd_43672 : Nat := 4429575732001652701069

theorem tailTrace_43672 : CollatzResearch.WordTrace tailWord_43672 prefixEnd_43672 4429575732001652701069 := by
  unfold tailWord_43672
  simp only [CollatzResearch.WordTrace]
  refine ⟨796424348895638714450635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1061899131860851619267513 796424348895638714450635)
  ·
    refine ⟨1194636523343458071675953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 796424348895638714450635 1194636523343458071675953)
    ·
      refine ⟨895977392507593553756965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1194636523343458071675953 895977392507593553756965)
      ·
        refine ⟨167995761095173791329431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 895977392507593553756965 167995761095173791329431)
        ·
          refine ⟨251993641642760686994147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167995761095173791329431 251993641642760686994147)
          ·
            refine ⟨377990462464141030491221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251993641642760686994147 377990462464141030491221)
            ·
              refine ⟨4429575732001652701069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 377990462464141030491221 4429575732001652701069)
              ·
                rfl

theorem cell19_43672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_43672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43672 prefixEnd_43672 := by exact prefixLift 43672
  have htrace : WordTrace (prefixWord ++ tailWord_43672) baseStart_43672 baseEnd_43672 := by
    simpa [prefixWord, tailWord_43672, baseEnd_43672] using wordTrace_append hprefix tailTrace_43672
  have hstable : (prefixWord ++ tailWord_43672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43672).length < 2 ^ (prefixWord ++ tailWord_43672).sum := by decide
  have hdescent : baseEnd_43672 < baseStart_43672 := by decide
  rcases family_descends (prefixWord ++ tailWord_43672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43702 : List Nat := [5, 1, 3, 1, 2, 2, 2, 3]
def baseStart_43702 : Nat := 118140960795 + 43702 * 2 ^ 59
def prefixEnd_43702 : Nat := 4983230072969 + 3 ^ 40 * 43702 * 2
def baseEnd_43702 : Nat := 13297855740973777436459

theorem tailTrace_43702 : CollatzResearch.WordTrace tailWord_43702 prefixEnd_43702 13297855740973777436459 := by
  unfold tailWord_43702
  simp only [CollatzResearch.WordTrace]
  refine ⟨99621430480162034530835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1062628591788395034995573 99621430480162034530835)
  ·
    refine ⟨149432145720243051796253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99621430480162034530835 149432145720243051796253)
    ·
      refine ⟨56037054645091144423595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149432145720243051796253 56037054645091144423595)
      ·
        refine ⟨84055581967636716635393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56037054645091144423595 84055581967636716635393)
        ·
          refine ⟨63041686475727537476545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84055581967636716635393 63041686475727537476545)
          ·
            refine ⟨47281264856795653107409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63041686475727537476545 47281264856795653107409)
            ·
              refine ⟨35460948642596739830557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47281264856795653107409 35460948642596739830557)
              ·
                refine ⟨13297855740973777436459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35460948642596739830557 13297855740973777436459)
                ·
                  rfl

theorem cell19_43702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_43702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43702 prefixEnd_43702 := by exact prefixLift 43702
  have htrace : WordTrace (prefixWord ++ tailWord_43702) baseStart_43702 baseEnd_43702 := by
    simpa [prefixWord, tailWord_43702, baseEnd_43702] using wordTrace_append hprefix tailTrace_43702
  have hstable : (prefixWord ++ tailWord_43702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43702).length < 2 ^ (prefixWord ++ tailWord_43702).sum := by decide
  have hdescent : baseEnd_43702 < baseStart_43702 := by decide
  rcases family_descends (prefixWord ++ tailWord_43702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43748 : List Nat := [2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_43748 : Nat := 118140960795 + 43748 * 2 ^ 59
def prefixEnd_43748 : Nat := 4983230072969 + 3 ^ 40 * 43748 * 2
def baseEnd_43748 : Nat := 13311852843259300414111

theorem tailTrace_43748 : CollatzResearch.WordTrace tailWord_43748 prefixEnd_43748 13311852843259300414111 := by
  unfold tailWord_43748
  simp only [CollatzResearch.WordTrace]
  refine ⟨797810322757971204333949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1063747097010628272445265 797810322757971204333949)
  ·
    refine ⟨299178871034239201625231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 797810322757971204333949 299178871034239201625231)
    ·
      refine ⟨448768306551358802437847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299178871034239201625231 448768306551358802437847)
      ·
        refine ⟨673152459827038203656771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448768306551358802437847 673152459827038203656771)
        ·
          refine ⟨1009728689740557305485157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673152459827038203656771 1009728689740557305485157)
          ·
            refine ⟨189324129326354494778467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1009728689740557305485157 189324129326354494778467)
            ·
              refine ⟨283986193989531742167701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189324129326354494778467 283986193989531742167701)
              ·
                refine ⟨13311852843259300414111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 283986193989531742167701 13311852843259300414111)
                ·
                  rfl

theorem cell19_43748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_43748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43748 prefixEnd_43748 := by exact prefixLift 43748
  have htrace : WordTrace (prefixWord ++ tailWord_43748) baseStart_43748 baseEnd_43748 := by
    simpa [prefixWord, tailWord_43748, baseEnd_43748] using wordTrace_append hprefix tailTrace_43748
  have hstable : (prefixWord ++ tailWord_43748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43748).length < 2 ^ (prefixWord ++ tailWord_43748).sum := by decide
  have hdescent : baseEnd_43748 < baseStart_43748 := by decide
  rcases family_descends (prefixWord ++ tailWord_43748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43818 : List Nat := [3, 1, 4, 3, 1, 1, 3, 3]
def baseStart_43818 : Nat := 118140960795 + 43818 * 2 ^ 59
def prefixEnd_43818 : Nat := 4983230072969 + 3 ^ 40 * 43818 * 2
def baseEnd_43818 : Nat := 13333152781519878858365

theorem tailTrace_43818 : CollatzResearch.WordTrace tailWord_43818 prefixEnd_43818 13333152781519878858365 := by
  unfold tailWord_43818
  simp only [CollatzResearch.WordTrace]
  refine ⟨399543438815586090929027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1065449170174896242477405 399543438815586090929027)
  ·
    refine ⟨599315158223379136393541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 399543438815586090929027 599315158223379136393541)
    ·
      refine ⟨112371592166883588073789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 599315158223379136393541 112371592166883588073789)
      ·
        refine ⟨42139347062581345527671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112371592166883588073789 42139347062581345527671)
        ·
          refine ⟨63209020593872018291507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42139347062581345527671 63209020593872018291507)
          ·
            refine ⟨94813530890808027437261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63209020593872018291507 94813530890808027437261)
            ·
              refine ⟨35555074084053010288973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94813530890808027437261 35555074084053010288973)
              ·
                refine ⟨13333152781519878858365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35555074084053010288973 13333152781519878858365)
                ·
                  rfl

theorem cell19_43818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_43818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43818 prefixEnd_43818 := by exact prefixLift 43818
  have htrace : WordTrace (prefixWord ++ tailWord_43818) baseStart_43818 baseEnd_43818 := by
    simpa [prefixWord, tailWord_43818, baseEnd_43818] using wordTrace_append hprefix tailTrace_43818
  have hstable : (prefixWord ++ tailWord_43818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43818).length < 2 ^ (prefixWord ++ tailWord_43818).sum := by decide
  have hdescent : baseEnd_43818 < baseStart_43818 := by decide
  rcases family_descends (prefixWord ++ tailWord_43818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43879 : List Nat := [1, 1, 5, 1, 2, 2, 4, 3]
def baseStart_43879 : Nat := 118140960795 + 43879 * 2 ^ 59
def prefixEnd_43879 : Nat := 4983230072969 + 3 ^ 40 * 43879 * 2
def baseEnd_43879 : Nat := 13351714156289811502643

theorem tailTrace_43879 : CollatzResearch.WordTrace tailWord_43879 prefixEnd_43879 13351714156289811502643 := by
  unfold tailWord_43879
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600398608041351781686691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1066932405360901187791127 1600398608041351781686691)
  ·
    refine ⟨2400597912062027672530037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1600398608041351781686691 2400597912062027672530037)
    ·
      refine ⟨225056054255815094299691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2400597912062027672530037 225056054255815094299691)
      ·
        refine ⟨337584081383722641449537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225056054255815094299691 337584081383722641449537)
        ·
          refine ⟨253188061037791981087153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337584081383722641449537 253188061037791981087153)
          ·
            refine ⟨189891045778343985815365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253188061037791981087153 189891045778343985815365)
            ·
              refine ⟨35604571083439497340381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189891045778343985815365 35604571083439497340381)
              ·
                refine ⟨13351714156289811502643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35604571083439497340381 13351714156289811502643)
                ·
                  rfl

theorem cell19_43879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_43879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43879 prefixEnd_43879 := by exact prefixLift 43879
  have htrace : WordTrace (prefixWord ++ tailWord_43879) baseStart_43879 baseEnd_43879 := by
    simpa [prefixWord, tailWord_43879, baseEnd_43879] using wordTrace_append hprefix tailTrace_43879
  have hstable : (prefixWord ++ tailWord_43879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43879).length < 2 ^ (prefixWord ++ tailWord_43879).sum := by decide
  have hdescent : baseEnd_43879 < baseStart_43879 := by decide
  rcases family_descends (prefixWord ++ tailWord_43879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43993 : List Nat := [1, 2, 1, 2, 5, 2, 3, 3]
def baseStart_43993 : Nat := 118140960795 + 43993 * 2 ^ 59
def prefixEnd_43993 : Nat := 4983230072969 + 3 ^ 40 * 43993 * 2
def baseEnd_43993 : Nat := 13386402627171324968999

theorem tailTrace_43993 : CollatzResearch.WordTrace tailWord_43993 prefixEnd_43993 13386402627171324968999 := by
  unfold tailWord_43993
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604556529628349251336633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1069704353085566167557755 1604556529628349251336633)
  ·
    refine ⟨1203417397221261938502475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1604556529628349251336633 1203417397221261938502475)
    ·
      refine ⟨1805126095831892907753713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203417397221261938502475 1805126095831892907753713)
      ·
        refine ⟨1353844571873919680815285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1805126095831892907753713 1353844571873919680815285)
        ·
          refine ⟨126922928613179970076433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1353844571873919680815285 126922928613179970076433)
          ·
            refine ⟨95192196459884977557325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126922928613179970076433 95192196459884977557325)
            ·
              refine ⟨35697073672456866583997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95192196459884977557325 35697073672456866583997)
              ·
                refine ⟨13386402627171324968999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35697073672456866583997 13386402627171324968999)
                ·
                  rfl

theorem cell19_43993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_43993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_43993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_43993 prefixEnd_43993 := by exact prefixLift 43993
  have htrace : WordTrace (prefixWord ++ tailWord_43993) baseStart_43993 baseEnd_43993 := by
    simpa [prefixWord, tailWord_43993, baseEnd_43993] using wordTrace_append hprefix tailTrace_43993
  have hstable : (prefixWord ++ tailWord_43993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43993).length < 2 ^ (prefixWord ++ tailWord_43993).sum := by decide
  have hdescent : baseEnd_43993 < baseStart_43993 := by decide
  rcases family_descends (prefixWord ++ tailWord_43993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44158 : List Nat := [4, 2, 4, 1, 1, 1, 3, 3]
def baseStart_44158 : Nat := 118140960795 + 44158 * 2 ^ 59
def prefixEnd_44158 : Nat := 4983230072969 + 3 ^ 40 * 44158 * 2
def baseEnd_44158 : Nat := 13436609624499831301883

theorem tailTrace_44158 : CollatzResearch.WordTrace tailWord_44158 prefixEnd_44158 13436609624499831301883 := by
  unfold tailWord_44158
  simp only [CollatzResearch.WordTrace]
  refine ⟨201321821753822803886641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1073716382687054954062085 201321821753822803886641)
  ·
    refine ⟨150991366315367102914981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201321821753822803886641 150991366315367102914981)
    ·
      refine ⟨28310881184131331796559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 150991366315367102914981 28310881184131331796559)
      ·
        refine ⟨42466321776196997694839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28310881184131331796559 42466321776196997694839)
        ·
          refine ⟨63699482664295496542259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42466321776196997694839 63699482664295496542259)
          ·
            refine ⟨95549223996443244813389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63699482664295496542259 95549223996443244813389)
            ·
              refine ⟨35830958998666216805021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95549223996443244813389 35830958998666216805021)
              ·
                refine ⟨13436609624499831301883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35830958998666216805021 13436609624499831301883)
                ·
                  rfl

theorem cell19_44158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_44158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44158 prefixEnd_44158 := by exact prefixLift 44158
  have htrace : WordTrace (prefixWord ++ tailWord_44158) baseStart_44158 baseEnd_44158 := by
    simpa [prefixWord, tailWord_44158, baseEnd_44158] using wordTrace_append hprefix tailTrace_44158
  have hstable : (prefixWord ++ tailWord_44158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44158).length < 2 ^ (prefixWord ++ tailWord_44158).sum := by decide
  have hdescent : baseEnd_44158 < baseStart_44158 := by decide
  rcases family_descends (prefixWord ++ tailWord_44158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44164 : List Nat := [2, 3, 2, 1, 2, 3, 3, 3]
def baseStart_44164 : Nat := 118140960795 + 44164 * 2 ^ 59
def prefixEnd_44164 : Nat := 4983230072969 + 3 ^ 40 * 44164 * 2
def baseEnd_44164 : Nat := 13438435333493595168533

theorem tailTrace_44164 : CollatzResearch.WordTrace tailWord_44164 prefixEnd_44164 13438435333493595168533 := by
  unfold tailWord_44164
  simp only [CollatzResearch.WordTrace]
  refine ⟨805396706004422727905773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1073862274672563637207697 805396706004422727905773)
  ·
    refine ⟨302023764751658522964665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 805396706004422727905773 302023764751658522964665)
    ·
      refine ⟨226517823563743892223499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302023764751658522964665 226517823563743892223499)
      ·
        refine ⟨339776735345615838335249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226517823563743892223499 339776735345615838335249)
        ·
          refine ⟨254832551509211878751437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339776735345615838335249 254832551509211878751437)
          ·
            refine ⟨95562206815954454531789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254832551509211878751437 95562206815954454531789)
            ·
              refine ⟨35835827555982920449421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95562206815954454531789 35835827555982920449421)
              ·
                refine ⟨13438435333493595168533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35835827555982920449421 13438435333493595168533)
                ·
                  rfl

theorem cell19_44164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_44164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44164 prefixEnd_44164 := by exact prefixLift 44164
  have htrace : WordTrace (prefixWord ++ tailWord_44164) baseStart_44164 baseEnd_44164 := by
    simpa [prefixWord, tailWord_44164, baseEnd_44164] using wordTrace_append hprefix tailTrace_44164
  have hstable : (prefixWord ++ tailWord_44164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44164).length < 2 ^ (prefixWord ++ tailWord_44164).sum := by decide
  have hdescent : baseEnd_44164 < baseStart_44164 := by decide
  rcases family_descends (prefixWord ++ tailWord_44164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44223 : List Nat := [1, 1, 2, 2, 2, 2, 6, 3]
def baseStart_44223 : Nat := 118140960795 + 44223 * 2 ^ 59
def prefixEnd_44223 : Nat := 4983230072969 + 3 ^ 40 * 44223 * 2
def baseEnd_44223 : Nat := 13456388138598939857261

theorem tailTrace_44223 : CollatzResearch.WordTrace tailWord_44223 prefixEnd_44223 13456388138598939857261 := by
  unfold tailWord_44223
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612945318795098532209323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1075296879196732354806215 1612945318795098532209323)
  ·
    refine ⟨2419417978192647798313985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1612945318795098532209323 2419417978192647798313985)
    ·
      refine ⟨1814563483644485848735489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2419417978192647798313985 1814563483644485848735489)
      ·
        refine ⟨1360922612733364386551617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1814563483644485848735489 1360922612733364386551617)
        ·
          refine ⟨1020691959550023289913713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1360922612733364386551617 1020691959550023289913713)
          ·
            refine ⟨765518969662517467435285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020691959550023289913713 765518969662517467435285)
            ·
              refine ⟨35883701702930506286029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 765518969662517467435285 35883701702930506286029)
              ·
                refine ⟨13456388138598939857261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35883701702930506286029 13456388138598939857261)
                ·
                  rfl

theorem cell19_44223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_44223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44223 prefixEnd_44223 := by exact prefixLift 44223
  have htrace : WordTrace (prefixWord ++ tailWord_44223) baseStart_44223 baseEnd_44223 := by
    simpa [prefixWord, tailWord_44223, baseEnd_44223] using wordTrace_append hprefix tailTrace_44223
  have hstable : (prefixWord ++ tailWord_44223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44223).length < 2 ^ (prefixWord ++ tailWord_44223).sum := by decide
  have hdescent : baseEnd_44223 < baseStart_44223 := by decide
  rcases family_descends (prefixWord ++ tailWord_44223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44282 : List Nat := [3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_44282 : Nat := 118140960795 + 44282 * 2 ^ 59
def prefixEnd_44282 : Nat := 4983230072969 + 3 ^ 40 * 44282 * 2
def baseEnd_44282 : Nat := 13474340943704284545989

theorem tailTrace_44282 : CollatzResearch.WordTrace tailWord_44282 prefixEnd_44282 13474340943704284545989 := by
  unfold tailWord_44282
  simp only [CollatzResearch.WordTrace]
  refine ⟨403774306395337902151775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1076731483720901072404733 403774306395337902151775)
  ·
    refine ⟨605661459593006853227663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403774306395337902151775 605661459593006853227663)
    ·
      refine ⟨908492189389510279841495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605661459593006853227663 908492189389510279841495)
      ·
        refine ⟨1362738284084265419762243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908492189389510279841495 1362738284084265419762243)
        ·
          refine ⟨2044107426126398129643365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362738284084265419762243 2044107426126398129643365)
          ·
            refine ⟨383270142398699649308131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2044107426126398129643365 383270142398699649308131)
            ·
              refine ⟨574905213598049473962197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383270142398699649308131 574905213598049473962197)
              ·
                refine ⟨13474340943704284545989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 574905213598049473962197 13474340943704284545989)
                ·
                  rfl

theorem cell19_44282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_44282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44282 prefixEnd_44282 := by exact prefixLift 44282
  have htrace : WordTrace (prefixWord ++ tailWord_44282) baseStart_44282 baseEnd_44282 := by
    simpa [prefixWord, tailWord_44282, baseEnd_44282] using wordTrace_append hprefix tailTrace_44282
  have hstable : (prefixWord ++ tailWord_44282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44282).length < 2 ^ (prefixWord ++ tailWord_44282).sum := by decide
  have hdescent : baseEnd_44282 < baseStart_44282 := by decide
  rcases family_descends (prefixWord ++ tailWord_44282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44333 : List Nat := [1, 5, 3, 1, 1, 2, 3, 3]
def baseStart_44333 : Nat := 118140960795 + 44333 * 2 ^ 59
def prefixEnd_44333 : Nat := 4983230072969 + 3 ^ 40 * 44333 * 2
def baseEnd_44333 : Nat := 13489859470151277412517

theorem tailTrace_44333 : CollatzResearch.WordTrace tailWord_44333 prefixEnd_44333 13489859470151277412517 := by
  unfold tailWord_44333
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616957348396587318713653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1077971565597724879142435 1616957348396587318713653)
  ·
    refine ⟨151589751412180061129405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1616957348396587318713653 151589751412180061129405)
    ·
      refine ⟨56846156779567522923527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151589751412180061129405 56846156779567522923527)
      ·
        refine ⟨85269235169351284385291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56846156779567522923527 85269235169351284385291)
        ·
          refine ⟨127903852754026926577937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85269235169351284385291 127903852754026926577937)
          ·
            refine ⟨95927889565520194933453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127903852754026926577937 95927889565520194933453)
            ·
              refine ⟨35972958587070073100045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95927889565520194933453 35972958587070073100045)
              ·
                refine ⟨13489859470151277412517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35972958587070073100045 13489859470151277412517)
                ·
                  rfl

theorem cell19_44333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_44333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44333 prefixEnd_44333 := by exact prefixLift 44333
  have htrace : WordTrace (prefixWord ++ tailWord_44333) baseStart_44333 baseEnd_44333 := by
    simpa [prefixWord, tailWord_44333, baseEnd_44333] using wordTrace_append hprefix tailTrace_44333
  have hstable : (prefixWord ++ tailWord_44333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44333).length < 2 ^ (prefixWord ++ tailWord_44333).sum := by decide
  have hdescent : baseEnd_44333 < baseStart_44333 := by decide
  rcases family_descends (prefixWord ++ tailWord_44333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44430 : List Nat := [4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_44430 : Nat := 118140960795 + 44430 * 2 ^ 59
def prefixEnd_44430 : Nat := 4983230072969 + 3 ^ 40 * 44430 * 2
def baseEnd_44430 : Nat := 13519375098883793256697

theorem tailTrace_44430 : CollatzResearch.WordTrace tailWord_44430 prefixEnd_44430 13519375098883793256697 := by
  unfold tailWord_44430
  simp only [CollatzResearch.WordTrace]
  refine ⟨202561903630646610624343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1080330152696781923329829 202561903630646610624343)
  ·
    refine ⟨303842855445969915936515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202561903630646610624343 303842855445969915936515)
    ·
      refine ⟨455764283168954873904773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303842855445969915936515 455764283168954873904773)
      ·
        refine ⟨85455803094179038857145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 455764283168954873904773 85455803094179038857145)
        ·
          refine ⟨64091852320634279142859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85455803094179038857145 64091852320634279142859)
          ·
            refine ⟨96137778480951418714289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64091852320634279142859 96137778480951418714289)
            ·
              refine ⟨72103333860713564035717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96137778480951418714289 72103333860713564035717)
              ·
                refine ⟨13519375098883793256697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72103333860713564035717 13519375098883793256697)
                ·
                  rfl

theorem cell19_44430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_44430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44430 prefixEnd_44430 := by exact prefixLift 44430
  have htrace : WordTrace (prefixWord ++ tailWord_44430) baseStart_44430 baseEnd_44430 := by
    simpa [prefixWord, tailWord_44430, baseEnd_44430] using wordTrace_append hprefix tailTrace_44430
  have hstable : (prefixWord ++ tailWord_44430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44430).length < 2 ^ (prefixWord ++ tailWord_44430).sum := by decide
  have hdescent : baseEnd_44430 < baseStart_44430 := by decide
  rcases family_descends (prefixWord ++ tailWord_44430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44491 : List Nat := [1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_44491 : Nat := 118140960795 + 44491 * 2 ^ 59
def prefixEnd_44491 : Nat := 4983230072969 + 3 ^ 40 * 44491 * 2
def baseEnd_44491 : Nat := 13537936473653725900975

theorem tailTrace_44491 : CollatzResearch.WordTrace tailWord_44491 prefixEnd_44491 13537936473653725900975 := by
  unfold tailWord_44491
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622720081824180302965327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1081813387882786868643551 1622720081824180302965327)
  ·
    refine ⟨2434080122736270454447991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1622720081824180302965327 2434080122736270454447991)
    ·
      refine ⟨3651120184104405681671987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434080122736270454447991 3651120184104405681671987)
      ·
        refine ⟨5476680276156608522507981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3651120184104405681671987 5476680276156608522507981)
        ·
          refine ⟨2053755103558728195940493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5476680276156608522507981 2053755103558728195940493)
          ·
            refine ⟨770158163834523073477685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2053755103558728195940493 770158163834523073477685)
            ·
              refine ⟨72202327859486538138533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 770158163834523073477685 72202327859486538138533)
              ·
                refine ⟨13537936473653725900975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72202327859486538138533 13537936473653725900975)
                ·
                  rfl

theorem cell19_44491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_44491 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44491 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44491 prefixEnd_44491 := by exact prefixLift 44491
  have htrace : WordTrace (prefixWord ++ tailWord_44491) baseStart_44491 baseEnd_44491 := by
    simpa [prefixWord, tailWord_44491, baseEnd_44491] using wordTrace_append hprefix tailTrace_44491
  have hstable : (prefixWord ++ tailWord_44491).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44491).length < 2 ^ (prefixWord ++ tailWord_44491).sum := by decide
  have hdescent : baseEnd_44491 < baseStart_44491 := by decide
  rcases family_descends (prefixWord ++ tailWord_44491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44529 : List Nat := [1, 2, 2, 2, 3, 3, 6]
def baseStart_44529 : Nat := 118140960795 + 44529 * 2 ^ 59
def prefixEnd_44529 : Nat := 4983230072969 + 3 ^ 40 * 44529 * 2
def baseEnd_44529 : Nat := 4516499765760299018809

theorem tailTrace_44529 : CollatzResearch.WordTrace tailWord_44529 prefixEnd_44529 4516499765760299018809 := by
  unfold tailWord_44529
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624106055686512792848641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1082737370457675195232427 1624106055686512792848641)
  ·
    refine ⟨1218079541764884594636481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1624106055686512792848641 1218079541764884594636481)
    ·
      refine ⟨913559656323663445977361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1218079541764884594636481 913559656323663445977361)
      ·
        refine ⟨685169742242747584483021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 913559656323663445977361 685169742242747584483021)
        ·
          refine ⟨256938653341030344181133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 685169742242747584483021 256938653341030344181133)
          ·
            refine ⟨96351995002886379067925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256938653341030344181133 96351995002886379067925)
            ·
              refine ⟨4516499765760299018809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96351995002886379067925 4516499765760299018809)
              ·
                rfl

theorem cell19_44529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_44529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44529 prefixEnd_44529 := by exact prefixLift 44529
  have htrace : WordTrace (prefixWord ++ tailWord_44529) baseStart_44529 baseEnd_44529 := by
    simpa [prefixWord, tailWord_44529, baseEnd_44529] using wordTrace_append hprefix tailTrace_44529
  have hstable : (prefixWord ++ tailWord_44529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44529).length < 2 ^ (prefixWord ++ tailWord_44529).sum := by decide
  have hdescent : baseEnd_44529 < baseStart_44529 := by decide
  rcases family_descends (prefixWord ++ tailWord_44529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44557 : List Nat := [1, 7, 1, 1, 3, 1, 2, 3]
def baseStart_44557 : Nat := 118140960795 + 44557 * 2 ^ 59
def prefixEnd_44557 : Nat := 4983230072969 + 3 ^ 40 * 44557 * 2
def baseEnd_44557 : Nat := 13558019272585128434129

theorem tailTrace_44557 : CollatzResearch.WordTrace tailWord_44557 prefixEnd_44557 13558019272585128434129 := by
  unfold tailWord_44557
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625127299585073574867925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1083418199723382383245283 1625127299585073574867925)
  ·
    refine ⟨38088921084025161910967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1625127299585073574867925 38088921084025161910967)
    ·
      refine ⟨57133381626037742866451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38088921084025161910967 57133381626037742866451)
      ·
        refine ⟨85700072439056614299677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57133381626037742866451 85700072439056614299677)
        ·
          refine ⟨32137527164646230362379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85700072439056614299677 32137527164646230362379)
          ·
            refine ⟨48206290746969345543569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32137527164646230362379 48206290746969345543569)
            ·
              refine ⟨36154718060227009157677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48206290746969345543569 36154718060227009157677)
              ·
                refine ⟨13558019272585128434129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36154718060227009157677 13558019272585128434129)
                ·
                  rfl

theorem cell19_44557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 3].length) (baseStart_44557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44557 prefixEnd_44557 := by exact prefixLift 44557
  have htrace : WordTrace (prefixWord ++ tailWord_44557) baseStart_44557 baseEnd_44557 := by
    simpa [prefixWord, tailWord_44557, baseEnd_44557] using wordTrace_append hprefix tailTrace_44557
  have hstable : (prefixWord ++ tailWord_44557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44557).length < 2 ^ (prefixWord ++ tailWord_44557).sum := by decide
  have hdescent : baseEnd_44557 < baseStart_44557 := by decide
  rcases family_descends (prefixWord ++ tailWord_44557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44565 : List Nat := [1, 3, 2, 1, 3, 2, 4, 3]
def baseStart_44565 : Nat := 118140960795 + 44565 * 2 ^ 59
def prefixEnd_44565 : Nat := 4983230072969 + 3 ^ 40 * 44565 * 2
def baseEnd_44565 : Nat := 13560453551243480256329

theorem tailTrace_44565 : CollatzResearch.WordTrace tailWord_44565 prefixEnd_44565 13560453551243480256329 := by
  unfold tailWord_44565
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625419083556090941159149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1083612722370727294106099 1625419083556090941159149)
  ·
    refine ⟨609532156333534102934681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1625419083556090941159149 609532156333534102934681)
    ·
      refine ⟨457149117250150577201011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 609532156333534102934681 457149117250150577201011)
      ·
        refine ⟨685723675875225865801517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457149117250150577201011 685723675875225865801517)
        ·
          refine ⟨257146378453209699675569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 685723675875225865801517 257146378453209699675569)
          ·
            refine ⟨192859783839907274756677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257146378453209699675569 192859783839907274756677)
            ·
              refine ⟨36161209469982614016877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192859783839907274756677 36161209469982614016877)
              ·
                refine ⟨13560453551243480256329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36161209469982614016877 13560453551243480256329)
                ·
                  rfl

theorem cell19_44565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_44565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44565 prefixEnd_44565 := by exact prefixLift 44565
  have htrace : WordTrace (prefixWord ++ tailWord_44565) baseStart_44565 baseEnd_44565 := by
    simpa [prefixWord, tailWord_44565, baseEnd_44565] using wordTrace_append hprefix tailTrace_44565
  have hstable : (prefixWord ++ tailWord_44565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44565).length < 2 ^ (prefixWord ++ tailWord_44565).sum := by decide
  have hdescent : baseEnd_44565 < baseStart_44565 := by decide
  rcases family_descends (prefixWord ++ tailWord_44565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44679 : List Nat := [1, 1, 4, 2, 1, 4, 3, 3]
def baseStart_44679 : Nat := 118140960795 + 44679 * 2 ^ 59
def prefixEnd_44679 : Nat := 4983230072969 + 3 ^ 40 * 44679 * 2
def baseEnd_44679 : Nat := 13595142022124993722685

theorem tailTrace_44679 : CollatzResearch.WordTrace tailWord_44679 prefixEnd_44679 13595142022124993722685 := by
  unfold tailWord_44679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629577005143088410809091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1086384670095392273872727 1629577005143088410809091)
  ·
    refine ⟨2444365507714632616213637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1629577005143088410809091 2444365507714632616213637)
    ·
      refine ⟨458318532696493615540057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2444365507714632616213637 458318532696493615540057)
      ·
        refine ⟨343738899522370211655043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458318532696493615540057 343738899522370211655043)
        ·
          refine ⟨515608349283555317482565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343738899522370211655043 515608349283555317482565)
          ·
            refine ⟨96676565490666622027981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 515608349283555317482565 96676565490666622027981)
            ·
              refine ⟨36253712058999983260493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96676565490666622027981 36253712058999983260493)
              ·
                refine ⟨13595142022124993722685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36253712058999983260493 13595142022124993722685)
                ·
                  rfl

theorem cell19_44679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_44679 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44679 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44679 prefixEnd_44679 := by exact prefixLift 44679
  have htrace : WordTrace (prefixWord ++ tailWord_44679) baseStart_44679 baseEnd_44679 := by
    simpa [prefixWord, tailWord_44679, baseEnd_44679] using wordTrace_append hprefix tailTrace_44679
  have hstable : (prefixWord ++ tailWord_44679).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44679).length < 2 ^ (prefixWord ++ tailWord_44679).sum := by decide
  have hdescent : baseEnd_44679 < baseStart_44679 := by decide
  rcases family_descends (prefixWord ++ tailWord_44679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44734 : List Nat := [4, 2, 1, 1, 2, 4, 2, 3]
def baseStart_44734 : Nat := 118140960795 + 44734 * 2 ^ 59
def prefixEnd_44734 : Nat := 4983230072969 + 3 ^ 40 * 44734 * 2
def baseEnd_44734 : Nat := 13611877687901162500313

theorem tailTrace_44734 : CollatzResearch.WordTrace tailWord_44734 prefixEnd_44734 13611877687901162500313 := by
  unfold tailWord_44734
  simp only [CollatzResearch.WordTrace]
  refine ⟨203947877492979100507657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1087722013295888536040837 203947877492979100507657)
  ·
    refine ⟨152960908119734325380743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203947877492979100507657 152960908119734325380743)
    ·
      refine ⟨229441362179601488071115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152960908119734325380743 229441362179601488071115)
      ·
        refine ⟨344162043269402232106673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229441362179601488071115 344162043269402232106673)
        ·
          refine ⟨258121532452051674080005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344162043269402232106673 258121532452051674080005)
          ·
            refine ⟨48397787334759688890001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258121532452051674080005 48397787334759688890001)
            ·
              refine ⟨36298340501069766667501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48397787334759688890001 36298340501069766667501)
              ·
                refine ⟨13611877687901162500313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36298340501069766667501 13611877687901162500313)
                ·
                  rfl

theorem cell19_44734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_44734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44734 prefixEnd_44734 := by exact prefixLift 44734
  have htrace : WordTrace (prefixWord ++ tailWord_44734) baseStart_44734 baseEnd_44734 := by
    simpa [prefixWord, tailWord_44734, baseEnd_44734] using wordTrace_append hprefix tailTrace_44734
  have hstable : (prefixWord ++ tailWord_44734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44734).length < 2 ^ (prefixWord ++ tailWord_44734).sum := by decide
  have hdescent : baseEnd_44734 < baseStart_44734 := by decide
  rcases family_descends (prefixWord ++ tailWord_44734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44776 : List Nat := [2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_44776 : Nat := 118140960795 + 44776 * 2 ^ 59
def prefixEnd_44776 : Nat := 4983230072969 + 3 ^ 40 * 44776 * 2
def baseEnd_44776 : Nat := 13624657650857509566865

theorem tailTrace_44776 : CollatzResearch.WordTrace tailWord_44776 prefixEnd_44776 13624657650857509566865 := by
  unfold tailWord_44776
  simp only [CollatzResearch.WordTrace]
  refine ⟨816557442895836988545091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1088743257194449318060121 816557442895836988545091)
  ·
    refine ⟨1224836164343755482817637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 816557442895836988545091 1224836164343755482817637)
    ·
      refine ⟨229656780814454153028307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1224836164343755482817637 229656780814454153028307)
      ·
        refine ⟨344485171221681229542461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229656780814454153028307 344485171221681229542461)
        ·
          refine ⟨129181939208130461078423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 344485171221681229542461 129181939208130461078423)
          ·
            refine ⟨193772908812195691617635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129181939208130461078423 193772908812195691617635)
            ·
              refine ⟨290659363218293537426453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193772908812195691617635 290659363218293537426453)
              ·
                refine ⟨13624657650857509566865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 290659363218293537426453 13624657650857509566865)
                ·
                  rfl

theorem cell19_44776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_44776 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44776 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44776 prefixEnd_44776 := by exact prefixLift 44776
  have htrace : WordTrace (prefixWord ++ tailWord_44776) baseStart_44776 baseEnd_44776 := by
    simpa [prefixWord, tailWord_44776, baseEnd_44776] using wordTrace_append hprefix tailTrace_44776
  have hstable : (prefixWord ++ tailWord_44776).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44776).length < 2 ^ (prefixWord ++ tailWord_44776).sum := by decide
  have hdescent : baseEnd_44776 < baseStart_44776 := by decide
  rcases family_descends (prefixWord ++ tailWord_44776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44806 : List Nat := [6, 2, 2, 1, 1, 7]
def baseStart_44806 : Nat := 118140960795 + 44806 * 2 ^ 59
def prefixEnd_44806 : Nat := 4983230072969 + 3 ^ 40 * 44806 * 2
def baseEnd_44806 : Nat := 1514865132869592100013

theorem tailTrace_44806 : CollatzResearch.WordTrace tailWord_44806 prefixEnd_44806 1514865132869592100013 := by
  unfold tailWord_44806
  simp only [CollatzResearch.WordTrace]
  refine ⟨51069033615093409396321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1089472717121992733788181 51069033615093409396321)
  ·
    refine ⟨38301775211320057047241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51069033615093409396321 38301775211320057047241)
    ·
      refine ⟨28726331408490042785431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38301775211320057047241 28726331408490042785431)
      ·
        refine ⟨43089497112735064178147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28726331408490042785431 43089497112735064178147)
        ·
          refine ⟨64634245669102596267221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43089497112735064178147 64634245669102596267221)
          ·
            refine ⟨1514865132869592100013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 64634245669102596267221 1514865132869592100013)
            ·
              rfl

theorem cell19_44806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 7].length) (baseStart_44806 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44806 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44806 prefixEnd_44806 := by exact prefixLift 44806
  have htrace : WordTrace (prefixWord ++ tailWord_44806) baseStart_44806 baseEnd_44806 := by
    simpa [prefixWord, tailWord_44806, baseEnd_44806] using wordTrace_append hprefix tailTrace_44806
  have hstable : (prefixWord ++ tailWord_44806).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44806).length < 2 ^ (prefixWord ++ tailWord_44806).sum := by decide
  have hdescent : baseEnd_44806 < baseStart_44806 := by decide
  rcases family_descends (prefixWord ++ tailWord_44806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44833 : List Nat := [1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_44833 : Nat := 118140960795 + 44833 * 2 ^ 59
def prefixEnd_44833 : Nat := 4983230072969 + 3 ^ 40 * 44833 * 2
def baseEnd_44833 : Nat := 13642001886298266300043

theorem tailTrace_44833 : CollatzResearch.WordTrace tailWord_44833 prefixEnd_44833 13642001886298266300043 := by
  unfold tailWord_44833
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635193846585172711915153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1090129231056781807943435 1635193846585172711915153)
  ·
    refine ⟨1226395384938879533936365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1635193846585172711915153 1226395384938879533936365)
    ·
      refine ⟨459898269352079825226137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1226395384938879533936365 459898269352079825226137)
      ·
        refine ⟨344923702014059868919603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459898269352079825226137 344923702014059868919603)
        ·
          refine ⟨517385553021089803379405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344923702014059868919603 517385553021089803379405)
          ·
            refine ⟨194019582382908676267277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517385553021089803379405 194019582382908676267277)
            ·
              refine ⟨72757343393590753600229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194019582382908676267277 72757343393590753600229)
              ·
                refine ⟨13642001886298266300043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72757343393590753600229 13642001886298266300043)
                ·
                  rfl

theorem cell19_44833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_44833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44833 prefixEnd_44833 := by exact prefixLift 44833
  have htrace : WordTrace (prefixWord ++ tailWord_44833) baseStart_44833 baseEnd_44833 := by
    simpa [prefixWord, tailWord_44833, baseEnd_44833] using wordTrace_append hprefix tailTrace_44833
  have hstable : (prefixWord ++ tailWord_44833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44833).length < 2 ^ (prefixWord ++ tailWord_44833).sum := by decide
  have hdescent : baseEnd_44833 < baseStart_44833 := by decide
  rcases family_descends (prefixWord ++ tailWord_44833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44850 : List Nat := [3, 2, 1, 1, 3, 3, 3, 3]
def baseStart_44850 : Nat := 118140960795 + 44850 * 2 ^ 59
def prefixEnd_44850 : Nat := 4983230072969 + 3 ^ 40 * 44850 * 2
def baseEnd_44850 : Nat := 13647174728447263922219

theorem tailTrace_44850 : CollatzResearch.WordTrace tailWord_44850 prefixEnd_44850 13647174728447263922219 := by
  unfold tailWord_44850
  simp only [CollatzResearch.WordTrace]
  refine ⟨408953471880896153821001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1090542591682389743522669 408953471880896153821001)
  ·
    refine ⟨306715103910672115365751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 408953471880896153821001 306715103910672115365751)
    ·
      refine ⟨460072655866008173048627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306715103910672115365751 460072655866008173048627)
      ·
        refine ⟨690108983799012259572941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460072655866008173048627 690108983799012259572941)
        ·
          refine ⟨258790868924629597339853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 690108983799012259572941 258790868924629597339853)
          ·
            refine ⟨97046575846736099002445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258790868924629597339853 97046575846736099002445)
            ·
              refine ⟨36392465942526037125917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97046575846736099002445 36392465942526037125917)
              ·
                refine ⟨13647174728447263922219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36392465942526037125917 13647174728447263922219)
                ·
                  rfl

theorem cell19_44850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_44850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44850 prefixEnd_44850 := by exact prefixLift 44850
  have htrace : WordTrace (prefixWord ++ tailWord_44850) baseStart_44850 baseEnd_44850 := by
    simpa [prefixWord, tailWord_44850, baseEnd_44850] using wordTrace_append hprefix tailTrace_44850
  have hstable : (prefixWord ++ tailWord_44850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44850).length < 2 ^ (prefixWord ++ tailWord_44850).sum := by decide
  have hdescent : baseEnd_44850 < baseStart_44850 := by decide
  rcases family_descends (prefixWord ++ tailWord_44850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44873 : List Nat := [1, 2, 1, 1, 2, 4, 8]
def baseStart_44873 : Nat := 118140960795 + 44873 * 2 ^ 59
def prefixEnd_44873 : Nat := 4983230072969 + 3 ^ 40 * 44873 * 2
def baseEnd_44873 : Nat := 4551391093196675137015

theorem tailTrace_44873 : CollatzResearch.WordTrace tailWord_44873 prefixEnd_44873 4551391093196675137015 := by
  unfold tailWord_44873
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636652766440259543371273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1091101844293506362247515 1636652766440259543371273)
  ·
    refine ⟨1227489574830194657528455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1636652766440259543371273 1227489574830194657528455)
    ·
      refine ⟨1841234362245291986292683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1227489574830194657528455 1841234362245291986292683)
      ·
        refine ⟨2761851543367937979439025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841234362245291986292683 2761851543367937979439025)
        ·
          refine ⟨2071388657525953484579269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2761851543367937979439025 2071388657525953484579269)
          ·
            refine ⟨388385373286116278358613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2071388657525953484579269 388385373286116278358613)
            ·
              refine ⟨4551391093196675137015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 388385373286116278358613 4551391093196675137015)
              ·
                rfl

theorem cell19_44873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_44873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44873 prefixEnd_44873 := by exact prefixLift 44873
  have htrace : WordTrace (prefixWord ++ tailWord_44873) baseStart_44873 baseEnd_44873 := by
    simpa [prefixWord, tailWord_44873, baseEnd_44873] using wordTrace_append hprefix tailTrace_44873
  have hstable : (prefixWord ++ tailWord_44873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44873).length < 2 ^ (prefixWord ++ tailWord_44873).sum := by decide
  have hdescent : baseEnd_44873 < baseStart_44873 := by decide
  rcases family_descends (prefixWord ++ tailWord_44873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44926 : List Nat := [4, 2, 3, 1, 1, 1, 7]
def baseStart_44926 : Nat := 118140960795 + 44926 * 2 ^ 59
def prefixEnd_44926 : Nat := 4983230072969 + 3 ^ 40 * 44926 * 2
def baseEnd_44926 : Nat := 4556766791900535411041

theorem tailTrace_44926 : CollatzResearch.WordTrace tailWord_44926 prefixEnd_44926 4556766791900535411041 := by
  unfold tailWord_44926
  simp only [CollatzResearch.WordTrace]
  refine ⟨204823229406031199381329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1092390556832166396700421 204823229406031199381329)
  ·
    refine ⟨153617422054523399535997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204823229406031199381329 153617422054523399535997)
    ·
      refine ⟨57606533270446274825999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153617422054523399535997 57606533270446274825999)
      ·
        refine ⟨86409799905669412238999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57606533270446274825999 86409799905669412238999)
        ·
          refine ⟨129614699858504118358499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86409799905669412238999 129614699858504118358499)
          ·
            refine ⟨194422049787756177537749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129614699858504118358499 194422049787756177537749)
            ·
              refine ⟨4556766791900535411041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 194422049787756177537749 4556766791900535411041)
              ·
                rfl

theorem cell19_44926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_44926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_44926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_44926 prefixEnd_44926 := by exact prefixLift 44926
  have htrace : WordTrace (prefixWord ++ tailWord_44926) baseStart_44926 baseEnd_44926 := by
    simpa [prefixWord, tailWord_44926, baseEnd_44926] using wordTrace_append hprefix tailTrace_44926
  have hstable : (prefixWord ++ tailWord_44926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44926).length < 2 ^ (prefixWord ++ tailWord_44926).sum := by decide
  have hdescent : baseEnd_44926 < baseStart_44926 := by decide
  rcases family_descends (prefixWord ++ tailWord_44926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45004 : List Nat := [2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_45004 : Nat := 118140960795 + 45004 * 2 ^ 59
def prefixEnd_45004 : Nat := 4983230072969 + 3 ^ 40 * 45004 * 2
def baseEnd_45004 : Nat := 13694034592620536499577

theorem tailTrace_45004 : CollatzResearch.WordTrace tailWord_45004 prefixEnd_45004 13694034592620536499577 := by
  unfold tailWord_45004
  simp only [CollatzResearch.WordTrace]
  refine ⟨820715364482834458195033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1094287152643779277593377 820715364482834458195033)
  ·
    refine ⟨615536523362125843646275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 820715364482834458195033 615536523362125843646275)
    ·
      refine ⟨923304785043188765469413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615536523362125843646275 923304785043188765469413)
      ·
        refine ⟨173119647195597893525515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 923304785043188765469413 173119647195597893525515)
        ·
          refine ⟨259679470793396840288273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173119647195597893525515 259679470793396840288273)
          ·
            refine ⟨194759603095047630216205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259679470793396840288273 194759603095047630216205)
            ·
              refine ⟨73034851160642861331077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194759603095047630216205 73034851160642861331077)
              ·
                refine ⟨13694034592620536499577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73034851160642861331077 13694034592620536499577)
                ·
                  rfl

theorem cell19_45004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_45004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45004 prefixEnd_45004 := by exact prefixLift 45004
  have htrace : WordTrace (prefixWord ++ tailWord_45004) baseStart_45004 baseEnd_45004 := by
    simpa [prefixWord, tailWord_45004, baseEnd_45004] using wordTrace_append hprefix tailTrace_45004
  have hstable : (prefixWord ++ tailWord_45004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45004).length < 2 ^ (prefixWord ++ tailWord_45004).sum := by decide
  have hdescent : baseEnd_45004 < baseStart_45004 := by decide
  rcases family_descends (prefixWord ++ tailWord_45004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45025 : List Nat := [1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_45025 : Nat := 118140960795 + 45025 * 2 ^ 59
def prefixEnd_45025 : Nat := 4983230072969 + 3 ^ 40 * 45025 * 2
def baseEnd_45025 : Nat := 13700424574098710032853

theorem tailTrace_45025 : CollatzResearch.WordTrace tailWord_45025 prefixEnd_45025 13700424574098710032853 := by
  unfold tailWord_45025
  simp only [CollatzResearch.WordTrace]
  refine ⟨1642196661889589502904529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1094797774593059668603019 1642196661889589502904529)
  ·
    refine ⟨1231647496417192127178397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1642196661889589502904529 1231647496417192127178397)
    ·
      refine ⟨461867811156447047691899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1231647496417192127178397 461867811156447047691899)
      ·
        refine ⟨692801716734670571537849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461867811156447047691899 692801716734670571537849)
        ·
          refine ⟨519601287551002928653387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692801716734670571537849 519601287551002928653387)
          ·
            refine ⟨779401931326504392980081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519601287551002928653387 779401931326504392980081)
            ·
              refine ⟨584551448494878294735061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779401931326504392980081 584551448494878294735061)
              ·
                refine ⟨13700424574098710032853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 584551448494878294735061 13700424574098710032853)
                ·
                  rfl

theorem cell19_45025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_45025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45025 prefixEnd_45025 := by exact prefixLift 45025
  have htrace : WordTrace (prefixWord ++ tailWord_45025) baseStart_45025 baseEnd_45025 := by
    simpa [prefixWord, tailWord_45025, baseEnd_45025] using wordTrace_append hprefix tailTrace_45025
  have hstable : (prefixWord ++ tailWord_45025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45025).length < 2 ^ (prefixWord ++ tailWord_45025).sum := by decide
  have hdescent : baseEnd_45025 < baseStart_45025 := by decide
  rcases family_descends (prefixWord ++ tailWord_45025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45076 : List Nat := [2, 4, 3, 2, 1, 1, 1, 5]
def baseStart_45076 : Nat := 118140960795 + 45076 * 2 ^ 59
def prefixEnd_45076 : Nat := 4983230072969 + 3 ^ 40 * 45076 * 2
def baseEnd_45076 : Nat := 13715943100545702899381

theorem tailTrace_45076 : CollatzResearch.WordTrace tailWord_45076 prefixEnd_45076 13715943100545702899381 := by
  unfold tailWord_45076
  simp only [CollatzResearch.WordTrace]
  refine ⟨822028392352412606505541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1096037856469883475340721 822028392352412606505541)
  ·
    refine ⟨154130323566077363719789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 822028392352412606505541 154130323566077363719789)
    ·
      refine ⟨57798871337279011394921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154130323566077363719789 57798871337279011394921)
      ·
        refine ⟨43349153502959258546191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57798871337279011394921 43349153502959258546191)
        ·
          refine ⟨65023730254438887819287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43349153502959258546191 65023730254438887819287)
          ·
            refine ⟨97535595381658331728931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65023730254438887819287 97535595381658331728931)
            ·
              refine ⟨146303393072487497593397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97535595381658331728931 146303393072487497593397)
              ·
                refine ⟨13715943100545702899381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146303393072487497593397 13715943100545702899381)
                ·
                  rfl

theorem cell19_45076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_45076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45076 prefixEnd_45076 := by exact prefixLift 45076
  have htrace : WordTrace (prefixWord ++ tailWord_45076) baseStart_45076 baseEnd_45076 := by
    simpa [prefixWord, tailWord_45076, baseEnd_45076] using wordTrace_append hprefix tailTrace_45076
  have hstable : (prefixWord ++ tailWord_45076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45076).length < 2 ^ (prefixWord ++ tailWord_45076).sum := by decide
  have hdescent : baseEnd_45076 < baseStart_45076 := by decide
  rcases family_descends (prefixWord ++ tailWord_45076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45095 : List Nat := [1, 1, 7, 1, 3, 1, 5]
def baseStart_45095 : Nat := 118140960795 + 45095 * 2 ^ 59
def prefixEnd_45095 : Nat := 4983230072969 + 3 ^ 40 * 45095 * 2
def baseEnd_45095 : Nat := 4573908170786429492369

theorem tailTrace_45095 : CollatzResearch.WordTrace tailWord_45095 prefixEnd_45095 4573908170786429492369 := by
  unfold tailWord_45095
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644749771635991457952739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1096499847757327638635159 1644749771635991457952739)
  ·
    refine ⟨2467124657453987186929109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1644749771635991457952739 2467124657453987186929109)
    ·
      refine ⟨57823234159077824693651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2467124657453987186929109 57823234159077824693651)
      ·
        refine ⟨86734851238616737040477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57823234159077824693651 86734851238616737040477)
        ·
          refine ⟨32525569214481276390179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86734851238616737040477 32525569214481276390179)
          ·
            refine ⟨48788353821721914585269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32525569214481276390179 48788353821721914585269)
            ·
              refine ⟨4573908170786429492369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48788353821721914585269 4573908170786429492369)
              ·
                rfl

theorem cell19_45095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 5].length) (baseStart_45095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45095 prefixEnd_45095 := by exact prefixLift 45095
  have htrace : WordTrace (prefixWord ++ tailWord_45095) baseStart_45095 baseEnd_45095 := by
    simpa [prefixWord, tailWord_45095, baseEnd_45095] using wordTrace_append hprefix tailTrace_45095
  have hstable : (prefixWord ++ tailWord_45095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45095).length < 2 ^ (prefixWord ++ tailWord_45095).sum := by decide
  have hdescent : baseEnd_45095 < baseStart_45095 := by decide
  rcases family_descends (prefixWord ++ tailWord_45095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45120 : List Nat := [2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_45120 : Nat := 118140960795 + 45120 * 2 ^ 59
def prefixEnd_45120 : Nat := 4983230072969 + 3 ^ 40 * 45120 * 2
def baseEnd_45120 : Nat := 13729331633166637921483

theorem tailTrace_45120 : CollatzResearch.WordTrace tailWord_45120 prefixEnd_45120 13729331633166637921483 := by
  unfold tailWord_45120
  simp only [CollatzResearch.WordTrace]
  refine ⟨822830798272710363806407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1097107731030280485075209 822830798272710363806407)
  ·
    refine ⟨1234246197409065545709611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 822830798272710363806407 1234246197409065545709611)
    ·
      refine ⟨1851369296113598318564417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1234246197409065545709611 1851369296113598318564417)
      ·
        refine ⟨1388526972085198738923313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1851369296113598318564417 1388526972085198738923313)
        ·
          refine ⟨1041395229063899054192485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388526972085198738923313 1041395229063899054192485)
          ·
            refine ⟨195261605449481072661091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1041395229063899054192485 195261605449481072661091)
            ·
              refine ⟨292892408174221608991637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195261605449481072661091 292892408174221608991637)
              ·
                refine ⟨13729331633166637921483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 292892408174221608991637 13729331633166637921483)
                ·
                  rfl

theorem cell19_45120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_45120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45120 prefixEnd_45120 := by exact prefixLift 45120
  have htrace : WordTrace (prefixWord ++ tailWord_45120) baseStart_45120 baseEnd_45120 := by
    simpa [prefixWord, tailWord_45120, baseEnd_45120] using wordTrace_append hprefix tailTrace_45120
  have hstable : (prefixWord ++ tailWord_45120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45120).length < 2 ^ (prefixWord ++ tailWord_45120).sum := by decide
  have hdescent : baseEnd_45120 < baseStart_45120 := by decide
  rcases family_descends (prefixWord ++ tailWord_45120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45154 : List Nat := [3, 3, 2, 2, 3, 6]
def baseStart_45154 : Nat := 118140960795 + 45154 * 2 ^ 59
def prefixEnd_45154 : Nat := 4983230072969 + 3 ^ 40 * 45154 * 2
def baseEnd_45154 : Nat := 1526630813051625907315

theorem tailTrace_45154 : CollatzResearch.WordTrace tailWord_45154 prefixEnd_45154 1526630813051625907315 := by
  unfold tailWord_45154
  simp only [CollatzResearch.WordTrace]
  refine ⟨411725419605561133587629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1097934452281496356233677 411725419605561133587629)
  ·
    refine ⟨154397032352085425095361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 411725419605561133587629 154397032352085425095361)
    ·
      refine ⟨115797774264064068821521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154397032352085425095361 115797774264064068821521)
      ·
        refine ⟨86848330698048051616141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115797774264064068821521 86848330698048051616141)
        ·
          refine ⟨32568124011768019356053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86848330698048051616141 32568124011768019356053)
          ·
            refine ⟨1526630813051625907315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32568124011768019356053 1526630813051625907315)
            ·
              rfl

theorem cell19_45154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 6].length) (baseStart_45154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45154 prefixEnd_45154 := by exact prefixLift 45154
  have htrace : WordTrace (prefixWord ++ tailWord_45154) baseStart_45154 baseEnd_45154 := by
    simpa [prefixWord, tailWord_45154, baseEnd_45154] using wordTrace_append hprefix tailTrace_45154
  have hstable : (prefixWord ++ tailWord_45154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45154).length < 2 ^ (prefixWord ++ tailWord_45154).sum := by decide
  have hdescent : baseEnd_45154 < baseStart_45154 := by decide
  rcases family_descends (prefixWord ++ tailWord_45154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45175 : List Nat := [1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_45175 : Nat := 118140960795 + 45175 * 2 ^ 59
def prefixEnd_45175 : Nat := 4983230072969 + 3 ^ 40 * 45175 * 2
def baseEnd_45175 : Nat := 13746067298942806699111

theorem tailTrace_45175 : CollatzResearch.WordTrace tailWord_45175 prefixEnd_45175 13746067298942806699111 := by
  unfold tailWord_45175
  simp only [CollatzResearch.WordTrace]
  refine ⟨1647667611346165120864979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1098445074230776747243319 1647667611346165120864979)
  ·
    refine ⟨2471501417019247681297469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1647667611346165120864979 2471501417019247681297469)
    ·
      refine ⟨926813031382217880486551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2471501417019247681297469 926813031382217880486551)
      ·
        refine ⟨1390219547073326820729827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926813031382217880486551 1390219547073326820729827)
        ·
          refine ⟨2085329320609990231094741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390219547073326820729827 2085329320609990231094741)
          ·
            refine ⟨48874905951796646041283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2085329320609990231094741 48874905951796646041283)
            ·
              refine ⟨73312358927694969061925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48874905951796646041283 73312358927694969061925)
              ·
                refine ⟨13746067298942806699111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73312358927694969061925 13746067298942806699111)
                ·
                  rfl

theorem cell19_45175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_45175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45175 prefixEnd_45175 := by exact prefixLift 45175
  have htrace : WordTrace (prefixWord ++ tailWord_45175) baseStart_45175 baseEnd_45175 := by
    simpa [prefixWord, tailWord_45175, baseEnd_45175] using wordTrace_append hprefix tailTrace_45175
  have hstable : (prefixWord ++ tailWord_45175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45175).length < 2 ^ (prefixWord ++ tailWord_45175).sum := by decide
  have hdescent : baseEnd_45175 < baseStart_45175 := by decide
  rcases family_descends (prefixWord ++ tailWord_45175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45192 : List Nat := [2, 1, 3, 4, 1, 2, 3, 3]
def baseStart_45192 : Nat := 118140960795 + 45192 * 2 ^ 59
def prefixEnd_45192 : Nat := 4983230072969 + 3 ^ 40 * 45192 * 2
def baseEnd_45192 : Nat := 13751240141091804321287

theorem tailTrace_45192 : CollatzResearch.WordTrace tailWord_45192 prefixEnd_45192 13751240141091804321287 := by
  unfold tailWord_45192
  simp only [CollatzResearch.WordTrace]
  refine ⟨824143826142288512116915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1098858434856384682822553 824143826142288512116915)
  ·
    refine ⟨1236215739213432768175373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 824143826142288512116915 1236215739213432768175373)
    ·
      refine ⟨463580902205037288065765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1236215739213432768175373 463580902205037288065765)
      ·
        refine ⟨86921419163444491512331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 463580902205037288065765 86921419163444491512331)
        ·
          refine ⟨130382128745166737268497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86921419163444491512331 130382128745166737268497)
          ·
            refine ⟨97786596558875052951373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130382128745166737268497 97786596558875052951373)
            ·
              refine ⟨36669973709578144856765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97786596558875052951373 36669973709578144856765)
              ·
                refine ⟨13751240141091804321287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36669973709578144856765 13751240141091804321287)
                ·
                  rfl

theorem cell19_45192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_45192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45192 prefixEnd_45192 := by exact prefixLift 45192
  have htrace : WordTrace (prefixWord ++ tailWord_45192) baseStart_45192 baseEnd_45192 := by
    simpa [prefixWord, tailWord_45192, baseEnd_45192] using wordTrace_append hprefix tailTrace_45192
  have hstable : (prefixWord ++ tailWord_45192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45192).length < 2 ^ (prefixWord ++ tailWord_45192).sum := by decide
  have hdescent : baseEnd_45192 < baseStart_45192 := by decide
  rcases family_descends (prefixWord ++ tailWord_45192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45234 : List Nat := [3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_45234 : Nat := 118140960795 + 45234 * 2 ^ 59
def prefixEnd_45234 : Nat := 4983230072969 + 3 ^ 40 * 45234 * 2
def baseEnd_45234 : Nat := 13764020104048151387839

theorem tailTrace_45234 : CollatzResearch.WordTrace tailWord_45234 prefixEnd_45234 13764020104048151387839 := by
  unfold tailWord_45234
  simp only [CollatzResearch.WordTrace]
  refine ⟨412454879533104549315689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1099879678754945464841837 412454879533104549315689)
  ·
    refine ⟨309341159649828411986767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 412454879533104549315689 309341159649828411986767)
    ·
      refine ⟨464011739474742617980151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309341159649828411986767 464011739474742617980151)
      ·
        refine ⟨696017609212113926970227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464011739474742617980151 696017609212113926970227)
        ·
          refine ⟨1044026413818170890455341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696017609212113926970227 1044026413818170890455341)
          ·
            refine ⟨391509905181814083920753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1044026413818170890455341 391509905181814083920753)
            ·
              refine ⟨293632428886360562940565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391509905181814083920753 293632428886360562940565)
              ·
                refine ⟨13764020104048151387839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 293632428886360562940565 13764020104048151387839)
                ·
                  rfl

theorem cell19_45234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_45234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45234 prefixEnd_45234 := by exact prefixLift 45234
  have htrace : WordTrace (prefixWord ++ tailWord_45234) baseStart_45234 baseEnd_45234 := by
    simpa [prefixWord, tailWord_45234, baseEnd_45234] using wordTrace_append hprefix tailTrace_45234
  have hstable : (prefixWord ++ tailWord_45234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45234).length < 2 ^ (prefixWord ++ tailWord_45234).sum := by decide
  have hdescent : baseEnd_45234 < baseStart_45234 := by decide
  rcases family_descends (prefixWord ++ tailWord_45234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45249 : List Nat := [1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_45249 : Nat := 118140960795 + 45249 * 2 ^ 59
def prefixEnd_45249 : Nat := 4983230072969 + 3 ^ 40 * 45249 * 2
def baseEnd_45249 : Nat := 13768584376532561054465

theorem tailTrace_45249 : CollatzResearch.WordTrace tailWord_45249 prefixEnd_45249 13768584376532561054465 := by
  unfold tailWord_45249
  simp only [CollatzResearch.WordTrace]
  refine ⟨1650366613078075759058801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1100244408718717172705867 1650366613078075759058801)
  ·
    refine ⟨1237774959808556819294101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1650366613078075759058801 1237774959808556819294101)
    ·
      refine ⟨58020701241026100904411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1237774959808556819294101 58020701241026100904411)
      ·
        refine ⟨87031051861539151356617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58020701241026100904411 87031051861539151356617)
        ·
          refine ⟨65273288896154363517463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87031051861539151356617 65273288896154363517463)
          ·
            refine ⟨97909933344231545276195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65273288896154363517463 97909933344231545276195)
            ·
              refine ⟨146864900016347317914293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97909933344231545276195 146864900016347317914293)
              ·
                refine ⟨13768584376532561054465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146864900016347317914293 13768584376532561054465)
                ·
                  rfl

theorem cell19_45249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_45249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45249 prefixEnd_45249 := by exact prefixLift 45249
  have htrace : WordTrace (prefixWord ++ tailWord_45249) baseStart_45249 baseEnd_45249 := by
    simpa [prefixWord, tailWord_45249, baseEnd_45249] using wordTrace_append hprefix tailTrace_45249
  have hstable : (prefixWord ++ tailWord_45249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45249).length < 2 ^ (prefixWord ++ tailWord_45249).sum := by decide
  have hdescent : baseEnd_45249 < baseStart_45249 := by decide
  rcases family_descends (prefixWord ++ tailWord_45249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45272 : List Nat := [2, 1, 2, 2, 4, 1, 7]
def baseStart_45272 : Nat := 118140960795 + 45272 * 2 ^ 59
def prefixEnd_45272 : Nat := 4983230072969 + 3 ^ 40 * 45272 * 2
def baseEnd_45272 : Nat := 4591860975891774181097

theorem tailTrace_45272 : CollatzResearch.WordTrace tailWord_45272 prefixEnd_45272 4591860975891774181097 := by
  unfold tailWord_45272
  simp only [CollatzResearch.WordTrace]
  refine ⟨825602745997375343573035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1100803661329833791430713 825602745997375343573035)
  ·
    refine ⟨1238404118996063015359553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 825602745997375343573035 1238404118996063015359553)
    ·
      refine ⟨928803089247047261519665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1238404118996063015359553 928803089247047261519665)
      ·
        refine ⟨696602316935285446139749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 928803089247047261519665 696602316935285446139749)
        ·
          refine ⟨130612934425366021151203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 696602316935285446139749 130612934425366021151203)
          ·
            refine ⟨195919401638049031726805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130612934425366021151203 195919401638049031726805)
            ·
              refine ⟨4591860975891774181097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 195919401638049031726805 4591860975891774181097)
              ·
                rfl

theorem cell19_45272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_45272 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45272 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45272 prefixEnd_45272 := by exact prefixLift 45272
  have htrace : WordTrace (prefixWord ++ tailWord_45272) baseStart_45272 baseEnd_45272 := by
    simpa [prefixWord, tailWord_45272, baseEnd_45272] using wordTrace_append hprefix tailTrace_45272
  have hstable : (prefixWord ++ tailWord_45272).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45272).length < 2 ^ (prefixWord ++ tailWord_45272).sum := by decide
  have hdescent : baseEnd_45272 < baseStart_45272 := by decide
  rcases family_descends (prefixWord ++ tailWord_45272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45291 : List Nat := [1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_45291 : Nat := 118140960795 + 45291 * 2 ^ 59
def prefixEnd_45291 : Nat := 4983230072969 + 3 ^ 40 * 45291 * 2
def baseEnd_45291 : Nat := 13781364339488908121017

theorem tailTrace_45291 : CollatzResearch.WordTrace tailWord_45291 prefixEnd_45291 13781364339488908121017 := by
  unfold tailWord_45291
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651898478925916932087727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1101265652617277954725151 1651898478925916932087727)
  ·
    refine ⟨2477847718388875398131591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1651898478925916932087727 2477847718388875398131591)
    ·
      refine ⟨3716771577583313097197387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2477847718388875398131591 3716771577583313097197387)
      ·
        refine ⟨5575157366374969645796081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3716771577583313097197387 5575157366374969645796081)
        ·
          refine ⟨4181368024781227234347061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5575157366374969645796081 4181368024781227234347061)
          ·
            refine ⟨392003252323240053220037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4181368024781227234347061 392003252323240053220037)
            ·
              refine ⟨73500609810607509978757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 392003252323240053220037 73500609810607509978757)
              ·
                refine ⟨13781364339488908121017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73500609810607509978757 13781364339488908121017)
                ·
                  rfl

theorem cell19_45291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_45291 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45291 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45291 prefixEnd_45291 := by exact prefixLift 45291
  have htrace : WordTrace (prefixWord ++ tailWord_45291) baseStart_45291 baseEnd_45291 := by
    simpa [prefixWord, tailWord_45291, baseEnd_45291] using wordTrace_append hprefix tailTrace_45291
  have hstable : (prefixWord ++ tailWord_45291).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45291).length < 2 ^ (prefixWord ++ tailWord_45291).sum := by decide
  have hdescent : baseEnd_45291 < baseStart_45291 := by decide
  rcases family_descends (prefixWord ++ tailWord_45291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45342 : List Nat := [4, 3, 2, 1, 1, 3, 1, 4]
def baseStart_45342 : Nat := 118140960795 + 45342 * 2 ^ 59
def prefixEnd_45342 : Nat := 4983230072969 + 3 ^ 40 * 45342 * 2
def baseEnd_45342 : Nat := 13796882865935900987545

theorem tailTrace_45342 : CollatzResearch.WordTrace tailWord_45342 prefixEnd_45342 13796882865935900987545 := by
  unfold tailWord_45342
  simp only [CollatzResearch.WordTrace]
  refine ⟨206719825217644080274285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1102505734494101761462853 206719825217644080274285)
  ·
    refine ⟨77519934456616530102857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206719825217644080274285 77519934456616530102857)
    ·
      refine ⟨58139950842462397577143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77519934456616530102857 58139950842462397577143)
      ·
        refine ⟨87209926263693596365715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58139950842462397577143 87209926263693596365715)
        ·
          refine ⟨130814889395540394548573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87209926263693596365715 130814889395540394548573)
          ·
            refine ⟨49055583523327647955715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130814889395540394548573 49055583523327647955715)
            ·
              refine ⟨73583375284991471933573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49055583523327647955715 73583375284991471933573)
              ·
                refine ⟨13796882865935900987545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73583375284991471933573 13796882865935900987545)
                ·
                  rfl

theorem cell19_45342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_45342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45342 prefixEnd_45342 := by exact prefixLift 45342
  have htrace : WordTrace (prefixWord ++ tailWord_45342) baseStart_45342 baseEnd_45342 := by
    simpa [prefixWord, tailWord_45342, baseEnd_45342] using wordTrace_append hprefix tailTrace_45342
  have hstable : (prefixWord ++ tailWord_45342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45342).length < 2 ^ (prefixWord ++ tailWord_45342).sum := by decide
  have hdescent : baseEnd_45342 < baseStart_45342 := by decide
  rcases family_descends (prefixWord ++ tailWord_45342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45346 : List Nat := [3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_45346 : Nat := 118140960795 + 45346 * 2 ^ 59
def prefixEnd_45346 : Nat := 4983230072969 + 3 ^ 40 * 45346 * 2
def baseEnd_45346 : Nat := 13798100005265076898645

theorem tailTrace_45346 : CollatzResearch.WordTrace tailWord_45346 prefixEnd_45346 13798100005265076898645 := by
  unfold tailWord_45346
  simp only [CollatzResearch.WordTrace]
  refine ⟨413476123431665331334973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1102602995817774216893261 413476123431665331334973)
  ·
    refine ⟨155053546286874499250615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 413476123431665331334973 155053546286874499250615)
    ·
      refine ⟨232580319430311748875923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155053546286874499250615 232580319430311748875923)
      ·
        refine ⟨348870479145467623313885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232580319430311748875923 348870479145467623313885)
        ·
          refine ⟨130826429679550358742707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348870479145467623313885 130826429679550358742707)
          ·
            refine ⟨196239644519325538114061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130826429679550358742707 196239644519325538114061)
            ·
              refine ⟨73589866694747076792773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196239644519325538114061 73589866694747076792773)
              ·
                refine ⟨13798100005265076898645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73589866694747076792773 13798100005265076898645)
                ·
                  rfl

theorem cell19_45346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_45346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45346 prefixEnd_45346 := by exact prefixLift 45346
  have htrace : WordTrace (prefixWord ++ tailWord_45346) baseStart_45346 baseEnd_45346 := by
    simpa [prefixWord, tailWord_45346, baseEnd_45346] using wordTrace_append hprefix tailTrace_45346
  have hstable : (prefixWord ++ tailWord_45346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45346).length < 2 ^ (prefixWord ++ tailWord_45346).sum := by decide
  have hdescent : baseEnd_45346 < baseStart_45346 := by decide
  rcases family_descends (prefixWord ++ tailWord_45346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45365 : List Nat := [1, 3, 3, 1, 2, 1, 5, 3]
def baseStart_45365 : Nat := 118140960795 + 45365 * 2 ^ 59
def prefixEnd_45365 : Nat := 4983230072969 + 3 ^ 40 * 45365 * 2
def baseEnd_45365 : Nat := 13803881417078662476371

theorem tailTrace_45365 : CollatzResearch.WordTrace tailWord_45365 prefixEnd_45365 13803881417078662476371 := by
  unfold tailWord_45365
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654597480657827570281549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1103064987105218380187699 1654597480657827570281549)
  ·
    refine ⟨620474055246685338855581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1654597480657827570281549 620474055246685338855581)
    ·
      refine ⟨232677770717507002070843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 620474055246685338855581 232677770717507002070843)
      ·
        refine ⟨349016656076260503106265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232677770717507002070843 349016656076260503106265)
        ·
          refine ⟨261762492057195377329699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349016656076260503106265 261762492057195377329699)
          ·
            refine ⟨392643738085793065994549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261762492057195377329699 392643738085793065994549)
            ·
              refine ⟨36810350445543099936989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 392643738085793065994549 36810350445543099936989)
              ·
                refine ⟨13803881417078662476371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36810350445543099936989 13803881417078662476371)
                ·
                  rfl

theorem cell19_45365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_45365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45365 prefixEnd_45365 := by exact prefixLift 45365
  have htrace : WordTrace (prefixWord ++ tailWord_45365) baseStart_45365 baseEnd_45365 := by
    simpa [prefixWord, tailWord_45365, baseEnd_45365] using wordTrace_append hprefix tailTrace_45365
  have hstable : (prefixWord ++ tailWord_45365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45365).length < 2 ^ (prefixWord ++ tailWord_45365).sum := by decide
  have hdescent : baseEnd_45365 < baseStart_45365 := by decide
  rcases family_descends (prefixWord ++ tailWord_45365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45420 : List Nat := [2, 2, 1, 1, 6, 2, 2, 3]
def baseStart_45420 : Nat := 118140960795 + 45420 * 2 ^ 59
def prefixEnd_45420 : Nat := 4983230072969 + 3 ^ 40 * 45420 * 2
def baseEnd_45420 : Nat := 13820617082854831253999

theorem tailTrace_45420 : CollatzResearch.WordTrace tailWord_45420 prefixEnd_45420 13820617082854831253999 := by
  unfold tailWord_45420
  simp only [CollatzResearch.WordTrace]
  refine ⟨828301747729285981766857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1104402330305714642355809 828301747729285981766857)
  ·
    refine ⟨621226310796964486325143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 828301747729285981766857 621226310796964486325143)
    ·
      refine ⟨931839466195446729487715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621226310796964486325143 931839466195446729487715)
      ·
        refine ⟨1397759199293170094231573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931839466195446729487715 1397759199293170094231573)
        ·
          refine ⟨65519962466867348167105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1397759199293170094231573 65519962466867348167105)
          ·
            refine ⟨49139971850150511125329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65519962466867348167105 49139971850150511125329)
            ·
              refine ⟨36854978887612883343997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49139971850150511125329 36854978887612883343997)
              ·
                refine ⟨13820617082854831253999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36854978887612883343997 13820617082854831253999)
                ·
                  rfl

theorem cell19_45420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_45420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45420 prefixEnd_45420 := by exact prefixLift 45420
  have htrace : WordTrace (prefixWord ++ tailWord_45420) baseStart_45420 baseEnd_45420 := by
    simpa [prefixWord, tailWord_45420, baseEnd_45420] using wordTrace_append hprefix tailTrace_45420
  have hstable : (prefixWord ++ tailWord_45420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45420).length < 2 ^ (prefixWord ++ tailWord_45420).sum := by decide
  have hdescent : baseEnd_45420 < baseStart_45420 := by decide
  rcases family_descends (prefixWord ++ tailWord_45420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45424 : List Nat := [2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_45424 : Nat := 118140960795 + 45424 * 2 ^ 59
def prefixEnd_45424 : Nat := 4983230072969 + 3 ^ 40 * 45424 * 2
def baseEnd_45424 : Nat := 13821834222184007165099

theorem tailTrace_45424 : CollatzResearch.WordTrace tailWord_45424 prefixEnd_45424 13821834222184007165099 := by
  unfold tailWord_45424
  simp only [CollatzResearch.WordTrace]
  refine ⟨828374693722040323339663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1104499591629387097786217 828374693722040323339663)
  ·
    refine ⟨1242562040583060485009495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 828374693722040323339663 1242562040583060485009495)
    ·
      refine ⟨1863843060874590727514243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1242562040583060485009495 1863843060874590727514243)
      ·
        refine ⟨2795764591311886091271365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863843060874590727514243 2795764591311886091271365)
        ·
          refine ⟨524205860870978642113381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2795764591311886091271365 524205860870978642113381)
          ·
            refine ⟨98288598913308495396259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 524205860870978642113381 98288598913308495396259)
            ·
              refine ⟨147432898369962743094389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98288598913308495396259 147432898369962743094389)
              ·
                refine ⟨13821834222184007165099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147432898369962743094389 13821834222184007165099)
                ·
                  rfl

theorem cell19_45424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_45424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45424 prefixEnd_45424 := by exact prefixLift 45424
  have htrace : WordTrace (prefixWord ++ tailWord_45424) baseStart_45424 baseEnd_45424 := by
    simpa [prefixWord, tailWord_45424, baseEnd_45424] using wordTrace_append hprefix tailTrace_45424
  have hstable : (prefixWord ++ tailWord_45424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45424).length < 2 ^ (prefixWord ++ tailWord_45424).sum := by decide
  have hdescent : baseEnd_45424 < baseStart_45424 := by decide
  rcases family_descends (prefixWord ++ tailWord_45424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45441 : List Nat := [1, 2, 4, 3, 1, 3, 5]
def baseStart_45441 : Nat := 118140960795 + 45441 * 2 ^ 59
def prefixEnd_45441 : Nat := 4983230072969 + 3 ^ 40 * 45441 * 2
def baseEnd_45441 : Nat := 4609002354777668262425

theorem tailTrace_45441 : CollatzResearch.WordTrace tailWord_45441 prefixEnd_45441 4609002354777668262425 := by
  unfold tailWord_45441
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657369428382492550048177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1104912952254995033365451 1657369428382492550048177)
  ·
    refine ⟨1243027071286869412536133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1657369428382492550048177 1243027071286869412536133)
    ·
      refine ⟨233067575866288014850525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1243027071286869412536133 233067575866288014850525)
      ·
        refine ⟨87400340949858005568947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233067575866288014850525 87400340949858005568947)
        ·
          refine ⟨131100511424787008353421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87400340949858005568947 131100511424787008353421)
          ·
            refine ⟨49162691784295128132533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131100511424787008353421 49162691784295128132533)
            ·
              refine ⟨4609002354777668262425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49162691784295128132533 4609002354777668262425)
              ·
                rfl

theorem cell19_45441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 5].length) (baseStart_45441 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45441 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45441 prefixEnd_45441 := by exact prefixLift 45441
  have htrace : WordTrace (prefixWord ++ tailWord_45441) baseStart_45441 baseEnd_45441 := by
    simpa [prefixWord, tailWord_45441, baseEnd_45441] using wordTrace_append hprefix tailTrace_45441
  have hstable : (prefixWord ++ tailWord_45441).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45441).length < 2 ^ (prefixWord ++ tailWord_45441).sum := by decide
  have hdescent : baseEnd_45441 < baseStart_45441 := by decide
  rcases family_descends (prefixWord ++ tailWord_45441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45500 : List Nat := [2, 2, 2, 4, 1, 8]
def baseStart_45500 : Nat := 118140960795 + 45500 * 2 ^ 59
def prefixEnd_45500 : Nat := 4983230072969 + 3 ^ 40 * 45500 * 2
def baseEnd_45500 : Nat := 1538328874382038830667

theorem tailTrace_45500 : CollatzResearch.WordTrace tailWord_45500 prefixEnd_45500 1538328874382038830667 := by
  unfold tailWord_45500
  simp only [CollatzResearch.WordTrace]
  refine ⟨829760667584372813222977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1106347556779163750963969 829760667584372813222977)
  ·
    refine ⟨622320500688279609917233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 829760667584372813222977 622320500688279609917233)
    ·
      refine ⟨466740375516209707437925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 622320500688279609917233 466740375516209707437925)
      ·
        refine ⟨87513820409289320144611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 466740375516209707437925 87513820409289320144611)
        ·
          refine ⟨131270730613933980216917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87513820409289320144611 131270730613933980216917)
          ·
            refine ⟨1538328874382038830667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 131270730613933980216917 1538328874382038830667)
            ·
              rfl

theorem cell19_45500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 8].length) (baseStart_45500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45500 prefixEnd_45500 := by exact prefixLift 45500
  have htrace : WordTrace (prefixWord ++ tailWord_45500) baseStart_45500 baseEnd_45500 := by
    simpa [prefixWord, tailWord_45500, baseEnd_45500] using wordTrace_append hprefix tailTrace_45500
  have hstable : (prefixWord ++ tailWord_45500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45500).length < 2 ^ (prefixWord ++ tailWord_45500).sum := by decide
  have hdescent : baseEnd_45500 < baseStart_45500 := by decide
  rcases family_descends (prefixWord ++ tailWord_45500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45616 : List Nat := [2, 1, 1, 1, 2, 3, 9]
def baseStart_45616 : Nat := 118140960795 + 45616 * 2 ^ 59
def prefixEnd_45616 : Nat := 4983230072969 + 3 ^ 40 * 45616 * 2
def baseEnd_45616 : Nat := 4626752303328150299303

theorem tailTrace_45616 : CollatzResearch.WordTrace tailWord_45616 prefixEnd_45616 4626752303328150299303 := by
  unfold tailWord_45616
  simp only [CollatzResearch.WordTrace]
  refine ⟨831876101374248718834351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1109168135165664958445801 831876101374248718834351)
  ·
    refine ⟨1247814152061373078251527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 831876101374248718834351 1247814152061373078251527)
    ·
      refine ⟨1871721228092059617377291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247814152061373078251527 1871721228092059617377291)
      ·
        refine ⟨2807581842138089426065937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871721228092059617377291 2807581842138089426065937)
        ·
          refine ⟨2105686381603567069549453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2807581842138089426065937 2105686381603567069549453)
          ·
            refine ⟨789632393101337651081045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2105686381603567069549453 789632393101337651081045)
            ·
              refine ⟨4626752303328150299303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 789632393101337651081045 4626752303328150299303)
              ·
                rfl

theorem cell19_45616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_45616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45616 prefixEnd_45616 := by exact prefixLift 45616
  have htrace : WordTrace (prefixWord ++ tailWord_45616) baseStart_45616 baseEnd_45616 := by
    simpa [prefixWord, tailWord_45616, baseEnd_45616] using wordTrace_append hprefix tailTrace_45616
  have hstable : (prefixWord ++ tailWord_45616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45616).length < 2 ^ (prefixWord ++ tailWord_45616).sum := by decide
  have hdescent : baseEnd_45616 < baseStart_45616 := by decide
  rcases family_descends (prefixWord ++ tailWord_45616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45633 : List Nat := [1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_45633 : Nat := 118140960795 + 45633 * 2 ^ 59
def prefixEnd_45633 : Nat := 4983230072969 + 3 ^ 40 * 45633 * 2
def baseEnd_45633 : Nat := 13885429752133448520085

theorem tailTrace_45633 : CollatzResearch.WordTrace tailWord_45633 prefixEnd_45633 13885429752133448520085 := by
  unfold tailWord_45633
  simp only [CollatzResearch.WordTrace]
  refine ⟨1664372243686909341037553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1109581495791272894025035 1664372243686909341037553)
  ·
    refine ⟨1248279182765182005778165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1664372243686909341037553 1248279182765182005778165)
    ·
      refine ⟨117026173384235813041703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1248279182765182005778165 117026173384235813041703)
      ·
        refine ⟨175539260076353719562555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117026173384235813041703 175539260076353719562555)
        ·
          refine ⟨263308890114530579343833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175539260076353719562555 263308890114530579343833)
          ·
            refine ⟨197481667585897934507875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263308890114530579343833 197481667585897934507875)
            ·
              refine ⟨296222501378846901761813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197481667585897934507875 296222501378846901761813)
              ·
                refine ⟨13885429752133448520085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 296222501378846901761813 13885429752133448520085)
                ·
                  rfl

theorem cell19_45633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_45633 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45633 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45633 prefixEnd_45633 := by exact prefixLift 45633
  have htrace : WordTrace (prefixWord ++ tailWord_45633) baseStart_45633 baseEnd_45633 := by
    simpa [prefixWord, tailWord_45633, baseEnd_45633] using wordTrace_append hprefix tailTrace_45633
  have hstable : (prefixWord ++ tailWord_45633).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45633).length < 2 ^ (prefixWord ++ tailWord_45633).sum := by decide
  have hdescent : baseEnd_45633 < baseStart_45633 := by decide
  rcases family_descends (prefixWord ++ tailWord_45633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45652 : List Nat := [2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_45652 : Nat := 118140960795 + 45652 * 2 ^ 59
def prefixEnd_45652 : Nat := 4983230072969 + 3 ^ 40 * 45652 * 2
def baseEnd_45652 : Nat := 13891211163947034097811

theorem tailTrace_45652 : CollatzResearch.WordTrace tailWord_45652 prefixEnd_45652 13891211163947034097811 := by
  unfold tailWord_45652
  simp only [CollatzResearch.WordTrace]
  refine ⟨832532615309037792989605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1110043487078717057319473 832532615309037792989605)
  ·
    refine ⟨156099865370444586185551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 832532615309037792989605 156099865370444586185551)
    ·
      refine ⟨234149798055666879278327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156099865370444586185551 234149798055666879278327)
      ·
        refine ⟨351224697083500318917491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234149798055666879278327 351224697083500318917491)
        ·
          refine ⟨526837045625250478376237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351224697083500318917491 526837045625250478376237)
          ·
            refine ⟨197563892109468929391089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 526837045625250478376237 197563892109468929391089)
            ·
              refine ⟨148172919082101697043317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197563892109468929391089 148172919082101697043317)
              ·
                refine ⟨13891211163947034097811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148172919082101697043317 13891211163947034097811)
                ·
                  rfl

theorem cell19_45652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_45652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45652 prefixEnd_45652 := by exact prefixLift 45652
  have htrace : WordTrace (prefixWord ++ tailWord_45652) baseStart_45652 baseEnd_45652 := by
    simpa [prefixWord, tailWord_45652, baseEnd_45652] using wordTrace_append hprefix tailTrace_45652
  have hstable : (prefixWord ++ tailWord_45652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45652).length < 2 ^ (prefixWord ++ tailWord_45652).sum := by decide
  have hdescent : baseEnd_45652 < baseStart_45652 := by decide
  rcases family_descends (prefixWord ++ tailWord_45652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45686 : List Nat := [5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_45686 : Nat := 118140960795 + 45686 * 2 ^ 59
def prefixEnd_45686 : Nat := 4983230072969 + 3 ^ 40 * 45686 * 2
def baseEnd_45686 : Nat := 13901556848245029342163

theorem tailTrace_45686 : CollatzResearch.WordTrace tailWord_45686 prefixEnd_45686 13901556848245029342163 := by
  unfold tailWord_45686
  simp only [CollatzResearch.WordTrace]
  refine ⟨104144082030931212044807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1110870208329932928477941 104144082030931212044807)
  ·
    refine ⟨156216123046396818067211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104144082030931212044807 156216123046396818067211)
    ·
      refine ⟨234324184569595227100817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156216123046396818067211 234324184569595227100817)
      ·
        refine ⟨175743138427196420325613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234324184569595227100817 175743138427196420325613)
        ·
          refine ⟨65903676910198657622105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175743138427196420325613 65903676910198657622105)
          ·
            refine ⟨49427757682648993216579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65903676910198657622105 49427757682648993216579)
            ·
              refine ⟨74141636523973489824869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49427757682648993216579 74141636523973489824869)
              ·
                refine ⟨13901556848245029342163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74141636523973489824869 13901556848245029342163)
                ·
                  rfl

theorem cell19_45686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_45686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45686 prefixEnd_45686 := by exact prefixLift 45686
  have htrace : WordTrace (prefixWord ++ tailWord_45686) baseStart_45686 baseEnd_45686 := by
    simpa [prefixWord, tailWord_45686, baseEnd_45686] using wordTrace_append hprefix tailTrace_45686
  have hstable : (prefixWord ++ tailWord_45686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45686).length < 2 ^ (prefixWord ++ tailWord_45686).sum := by decide
  have hdescent : baseEnd_45686 < baseStart_45686 := by decide
  rcases family_descends (prefixWord ++ tailWord_45686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45728 : List Nat := [2, 1, 1, 4, 4, 1, 6]
def baseStart_45728 : Nat := 118140960795 + 45728 * 2 ^ 59
def prefixEnd_45728 : Nat := 4983230072969 + 3 ^ 40 * 45728 * 2
def baseEnd_45728 : Nat := 4638112270400458802905

theorem tailTrace_45728 : CollatzResearch.WordTrace tailWord_45728 prefixEnd_45728 4638112270400458802905 := by
  unfold tailWord_45728
  simp only [CollatzResearch.WordTrace]
  refine ⟨833918589171370282872919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1111891452228493710497225 833918589171370282872919)
  ·
    refine ⟨1250877883757055424309379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833918589171370282872919 1250877883757055424309379)
    ·
      refine ⟨1876316825635583136464069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250877883757055424309379 1876316825635583136464069)
      ·
        refine ⟨351809404806671838087013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1876316825635583136464069 351809404806671838087013)
        ·
          refine ⟨65964263401250969641315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 351809404806671838087013 65964263401250969641315)
          ·
            refine ⟨98946395101876454461973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65964263401250969641315 98946395101876454461973)
            ·
              refine ⟨4638112270400458802905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98946395101876454461973 4638112270400458802905)
              ·
                rfl

theorem cell19_45728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_45728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45728 prefixEnd_45728 := by exact prefixLift 45728
  have htrace : WordTrace (prefixWord ++ tailWord_45728) baseStart_45728 baseEnd_45728 := by
    simpa [prefixWord, tailWord_45728, baseEnd_45728] using wordTrace_append hprefix tailTrace_45728
  have hstable : (prefixWord ++ tailWord_45728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45728).length < 2 ^ (prefixWord ++ tailWord_45728).sum := by decide
  have hdescent : baseEnd_45728 < baseStart_45728 := by decide
  rcases family_descends (prefixWord ++ tailWord_45728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45764 : List Nat := [2, 3, 3, 1, 1, 2, 4, 3]
def baseStart_45764 : Nat := 118140960795 + 45764 * 2 ^ 59
def prefixEnd_45764 : Nat := 4983230072969 + 3 ^ 40 * 45764 * 2
def baseEnd_45764 : Nat := 13925291065163959608617

theorem tailTrace_45764 : CollatzResearch.WordTrace tailWord_45764 prefixEnd_45764 13925291065163959608617 := by
  unfold tailWord_45764
  simp only [CollatzResearch.WordTrace]
  refine ⟨834575103106159357028173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1112766804141545809370897 834575103106159357028173)
  ·
    refine ⟨312965663664809758885565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 834575103106159357028173 312965663664809758885565)
    ·
      refine ⟨117362123874303659582087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312965663664809758885565 117362123874303659582087)
      ·
        refine ⟨176043185811455489373131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117362123874303659582087 176043185811455489373131)
        ·
          refine ⟨264064778717183234059697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176043185811455489373131 264064778717183234059697)
          ·
            refine ⟨198048584037887425544773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264064778717183234059697 198048584037887425544773)
            ·
              refine ⟨37134109507103892289645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198048584037887425544773 37134109507103892289645)
              ·
                refine ⟨13925291065163959608617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37134109507103892289645 13925291065163959608617)
                ·
                  rfl

theorem cell19_45764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_45764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45764 prefixEnd_45764 := by exact prefixLift 45764
  have htrace : WordTrace (prefixWord ++ tailWord_45764) baseStart_45764 baseEnd_45764 := by
    simpa [prefixWord, tailWord_45764, baseEnd_45764] using wordTrace_append hprefix tailTrace_45764
  have hstable : (prefixWord ++ tailWord_45764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45764).length < 2 ^ (prefixWord ++ tailWord_45764).sum := by decide
  have hdescent : baseEnd_45764 < baseStart_45764 := by decide
  rcases family_descends (prefixWord ++ tailWord_45764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45781 : List Nat := [1, 3, 2, 5, 2, 1, 5]
def baseStart_45781 : Nat := 118140960795 + 45781 * 2 ^ 59
def prefixEnd_45781 : Nat := 4983230072969 + 3 ^ 40 * 45781 * 2
def baseEnd_45781 : Nat := 4643487969104319076931

theorem tailTrace_45781 : CollatzResearch.WordTrace tailWord_45781 prefixEnd_45781 4643487969104319076931 := by
  unfold tailWord_45781
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669770247150730617425197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1113180164767153744950131 1669770247150730617425197)
  ·
    refine ⟨626163842681523981534449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1669770247150730617425197 626163842681523981534449)
    ·
      refine ⟨469622882011142986150837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 626163842681523981534449 469622882011142986150837)
      ·
        refine ⟨44027145188544654951641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 469622882011142986150837 44027145188544654951641)
        ·
          refine ⟨33020358891408491213731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44027145188544654951641 33020358891408491213731)
          ·
            refine ⟨49530538337112736820597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33020358891408491213731 49530538337112736820597)
            ·
              refine ⟨4643487969104319076931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49530538337112736820597 4643487969104319076931)
              ·
                rfl

theorem cell19_45781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 5].length) (baseStart_45781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45781 prefixEnd_45781 := by exact prefixLift 45781
  have htrace : WordTrace (prefixWord ++ tailWord_45781) baseStart_45781 baseEnd_45781 := by
    simpa [prefixWord, tailWord_45781, baseEnd_45781] using wordTrace_append hprefix tailTrace_45781
  have hstable : (prefixWord ++ tailWord_45781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45781).length < 2 ^ (prefixWord ++ tailWord_45781).sum := by decide
  have hdescent : baseEnd_45781 < baseStart_45781 := by decide
  rcases family_descends (prefixWord ++ tailWord_45781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45842 : List Nat := [3, 2, 4, 1, 9]
def baseStart_45842 : Nat := 118140960795 + 45842 * 2 ^ 59
def prefixEnd_45842 : Nat := 4983230072969 + 3 ^ 40 * 45842 * 2
def baseEnd_45842 : Nat := 516630566003069995373

theorem tailTrace_45842 : CollatzResearch.WordTrace tailWord_45842 prefixEnd_45842 516630566003069995373 := by
  unfold tailWord_45842
  simp only [CollatzResearch.WordTrace]
  refine ⟨417998774982434508848945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1114663399953158690263853 417998774982434508848945)
  ·
    refine ⟨313499081236825881636709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 417998774982434508848945 313499081236825881636709)
    ·
      refine ⟨58781077731904852806883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313499081236825881636709 58781077731904852806883)
      ·
        refine ⟨88171616597857279210325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58781077731904852806883 88171616597857279210325)
        ·
          refine ⟨516630566003069995373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 88171616597857279210325 516630566003069995373)
          ·
            rfl

theorem cell19_45842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 9].length) (baseStart_45842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45842 prefixEnd_45842 := by exact prefixLift 45842
  have htrace : WordTrace (prefixWord ++ tailWord_45842) baseStart_45842 baseEnd_45842 := by
    simpa [prefixWord, tailWord_45842, baseEnd_45842] using wordTrace_append hprefix tailTrace_45842
  have hstable : (prefixWord ++ tailWord_45842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45842).length < 2 ^ (prefixWord ++ tailWord_45842).sum := by decide
  have hdescent : baseEnd_45842 < baseStart_45842 := by decide
  rcases family_descends (prefixWord ++ tailWord_45842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45876 : List Nat := [2, 5, 1, 1, 3, 1, 3, 3]
def baseStart_45876 : Nat := 118140960795 + 45876 * 2 ^ 59
def prefixEnd_45876 : Nat := 4983230072969 + 3 ^ 40 * 45876 * 2
def baseEnd_45876 : Nat := 13959370966380885119423

theorem tailTrace_45876 : CollatzResearch.WordTrace tailWord_45876 prefixEnd_45876 13959370966380885119423 := by
  unfold tailWord_45876
  simp only [CollatzResearch.WordTrace]
  refine ⟨836617590903280921066741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1115490121204374561422321 836617590903280921066741)
  ·
    refine ⟨78432899147182586350007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 836617590903280921066741 78432899147182586350007)
    ·
      refine ⟨117649348720773879525011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78432899147182586350007 117649348720773879525011)
      ·
        refine ⟨176474023081160819287517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117649348720773879525011 176474023081160819287517)
        ·
          refine ⟨66177758655435307232819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176474023081160819287517 66177758655435307232819)
          ·
            refine ⟨99266637983152960849229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66177758655435307232819 99266637983152960849229)
            ·
              refine ⟨37224989243682360318461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99266637983152960849229 37224989243682360318461)
              ·
                refine ⟨13959370966380885119423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37224989243682360318461 13959370966380885119423)
                ·
                  rfl

theorem cell19_45876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_45876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45876 prefixEnd_45876 := by exact prefixLift 45876
  have htrace : WordTrace (prefixWord ++ tailWord_45876) baseStart_45876 baseEnd_45876 := by
    simpa [prefixWord, tailWord_45876, baseEnd_45876] using wordTrace_append hprefix tailTrace_45876
  have hstable : (prefixWord ++ tailWord_45876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45876).length < 2 ^ (prefixWord ++ tailWord_45876).sum := by decide
  have hdescent : baseEnd_45876 < baseStart_45876 := by decide
  rcases family_descends (prefixWord ++ tailWord_45876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45880 : List Nat := [2, 1, 2, 1, 3, 2, 5, 3]
def baseStart_45880 : Nat := 118140960795 + 45880 * 2 ^ 59
def prefixEnd_45880 : Nat := 4983230072969 + 3 ^ 40 * 45880 * 2
def baseEnd_45880 : Nat := 13960588105710061030523

theorem tailTrace_45880 : CollatzResearch.WordTrace tailWord_45880 prefixEnd_45880 13960588105710061030523 := by
  unfold tailWord_45880
  simp only [CollatzResearch.WordTrace]
  refine ⟨836690536896035262639547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1115587382528047016852729 836690536896035262639547)
  ·
    refine ⟨1255035805344052893959321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 836690536896035262639547 1255035805344052893959321)
    ·
      refine ⟨941276854008039670469491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1255035805344052893959321 941276854008039670469491)
      ·
        refine ⟨1411915281012059505704237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941276854008039670469491 1411915281012059505704237)
        ·
          refine ⟨529468230379522314639089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1411915281012059505704237 529468230379522314639089)
          ·
            refine ⟨397101172784641735979317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529468230379522314639089 397101172784641735979317)
            ·
              refine ⟨37228234948560162748061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 397101172784641735979317 37228234948560162748061)
              ·
                refine ⟨13960588105710061030523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37228234948560162748061 13960588105710061030523)
                ·
                  rfl

theorem cell19_45880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_45880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45880 prefixEnd_45880 := by exact prefixLift 45880
  have htrace : WordTrace (prefixWord ++ tailWord_45880) baseStart_45880 baseEnd_45880 := by
    simpa [prefixWord, tailWord_45880, baseEnd_45880] using wordTrace_append hprefix tailTrace_45880
  have hstable : (prefixWord ++ tailWord_45880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45880).length < 2 ^ (prefixWord ++ tailWord_45880).sum := by decide
  have hdescent : baseEnd_45880 < baseStart_45880 := by decide
  rcases family_descends (prefixWord ++ tailWord_45880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45920 : List Nat := [2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_45920 : Nat := 118140960795 + 45920 * 2 ^ 59
def prefixEnd_45920 : Nat := 4983230072969 + 3 ^ 40 * 45920 * 2
def baseEnd_45920 : Nat := 13972759499001820141525

theorem tailTrace_45920 : CollatzResearch.WordTrace tailWord_45920 prefixEnd_45920 13972759499001820141525 := by
  unfold tailWord_45920
  simp only [CollatzResearch.WordTrace]
  refine ⟨837419996823578678367607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1116559995764771571156809 837419996823578678367607)
  ·
    refine ⟨1256129995235368017551411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 837419996823578678367607 1256129995235368017551411)
    ·
      refine ⟨1884194992853052026327117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256129995235368017551411 1884194992853052026327117)
      ·
        refine ⟨706573122319894509872669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1884194992853052026327117 706573122319894509872669)
        ·
          refine ⟨264964920869960441202251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 706573122319894509872669 264964920869960441202251)
          ·
            refine ⟨397447381304940661803377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264964920869960441202251 397447381304940661803377)
            ·
              refine ⟨298085535978705496352533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397447381304940661803377 298085535978705496352533)
              ·
                refine ⟨13972759499001820141525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 298085535978705496352533 13972759499001820141525)
                ·
                  rfl

theorem cell19_45920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_45920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45920 prefixEnd_45920 := by exact prefixLift 45920
  have htrace : WordTrace (prefixWord ++ tailWord_45920) baseStart_45920 baseEnd_45920 := by
    simpa [prefixWord, tailWord_45920, baseEnd_45920] using wordTrace_append hprefix tailTrace_45920
  have hstable : (prefixWord ++ tailWord_45920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45920).length < 2 ^ (prefixWord ++ tailWord_45920).sum := by decide
  have hdescent : baseEnd_45920 < baseStart_45920 := by decide
  rcases family_descends (prefixWord ++ tailWord_45920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45937 : List Nat := [1, 2, 2, 2, 1, 4, 4, 3]
def baseStart_45937 : Nat := 118140960795 + 45937 * 2 ^ 59
def prefixEnd_45937 : Nat := 4983230072969 + 3 ^ 40 * 45937 * 2
def baseEnd_45937 : Nat := 13977932341150817763701

theorem tailTrace_45937 : CollatzResearch.WordTrace tailWord_45937 prefixEnd_45937 13977932341150817763701 := by
  unfold tailWord_45937
  simp only [CollatzResearch.WordTrace]
  refine ⟨1675460034585569260104065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1116973356390379506736043 1675460034585569260104065)
  ·
    refine ⟨1256595025939176945078049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1675460034585569260104065 1256595025939176945078049)
    ·
      refine ⟨942446269454382708808537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1256595025939176945078049 942446269454382708808537)
      ·
        refine ⟨706834702090787031606403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 942446269454382708808537 706834702090787031606403)
        ·
          refine ⟨1060252053136180547409605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706834702090787031606403 1060252053136180547409605)
          ·
            refine ⟨198797259963033852639301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1060252053136180547409605 198797259963033852639301)
            ·
              refine ⟨37274486243068847369869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198797259963033852639301 37274486243068847369869)
              ·
                refine ⟨13977932341150817763701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37274486243068847369869 13977932341150817763701)
                ·
                  rfl

theorem cell19_45937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_45937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_45937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_45937 prefixEnd_45937 := by exact prefixLift 45937
  have htrace : WordTrace (prefixWord ++ tailWord_45937) baseStart_45937 baseEnd_45937 := by
    simpa [prefixWord, tailWord_45937, baseEnd_45937] using wordTrace_append hprefix tailTrace_45937
  have hstable : (prefixWord ++ tailWord_45937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45937).length < 2 ^ (prefixWord ++ tailWord_45937).sum := by decide
  have hdescent : baseEnd_45937 < baseStart_45937 := by decide
  rcases family_descends (prefixWord ++ tailWord_45937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46013 : List Nat := [1, 4, 1, 2, 5, 6]
def baseStart_46013 : Nat := 118140960795 + 46013 * 2 ^ 59
def prefixEnd_46013 : Nat := 4983230072969 + 3 ^ 40 * 46013 * 2
def baseEnd_46013 : Nat := 1555673109822795563845

theorem tailTrace_46013 : CollatzResearch.WordTrace tailWord_46013 prefixEnd_46013 1555673109822795563845 := by
  unfold tailWord_46013
  simp only [CollatzResearch.WordTrace]
  refine ⟨1678231982310234239870693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1118821321540156159913795 1678231982310234239870693)
  ·
    refine ⟨314668496683168919975755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1678231982310234239870693 314668496683168919975755)
    ·
      refine ⟨472002745024753379963633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314668496683168919975755 472002745024753379963633)
      ·
        refine ⟨354002058768565034972725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472002745024753379963633 354002058768565034972725)
        ·
          refine ⟨33187693009552972028693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 354002058768565034972725 33187693009552972028693)
          ·
            refine ⟨1555673109822795563845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33187693009552972028693 1555673109822795563845)
            ·
              rfl

theorem cell19_46013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 6].length) (baseStart_46013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46013 prefixEnd_46013 := by exact prefixLift 46013
  have htrace : WordTrace (prefixWord ++ tailWord_46013) baseStart_46013 baseEnd_46013 := by
    simpa [prefixWord, tailWord_46013, baseEnd_46013] using wordTrace_append hprefix tailTrace_46013
  have hstable : (prefixWord ++ tailWord_46013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46013).length < 2 ^ (prefixWord ++ tailWord_46013).sum := by decide
  have hdescent : baseEnd_46013 < baseStart_46013 := by decide
  rcases family_descends (prefixWord ++ tailWord_46013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46022 : List Nat := [6, 1, 3, 1, 2, 1, 1, 4]
def baseStart_46022 : Nat := 118140960795 + 46022 * 2 ^ 59
def prefixEnd_46022 : Nat := 4983230072969 + 3 ^ 40 * 46022 * 2
def baseEnd_46022 : Nat := 14003796551895805874581

theorem tailTrace_46022 : CollatzResearch.WordTrace tailWord_46022 prefixEnd_46022 14003796551895805874581 := by
  unfold tailWord_46022
  simp only [CollatzResearch.WordTrace]
  refine ⟨52455007477425899279635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1119040159518419184632213 52455007477425899279635)
  ·
    refine ⟨78682511216138848919453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52455007477425899279635 78682511216138848919453)
    ·
      refine ⟨29505941706052068344795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78682511216138848919453 29505941706052068344795)
      ·
        refine ⟨44258912559078102517193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29505941706052068344795 44258912559078102517193)
        ·
          refine ⟨33194184419308576887895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44258912559078102517193 33194184419308576887895)
          ·
            refine ⟨49791276628962865331843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33194184419308576887895 49791276628962865331843)
            ·
              refine ⟨74686914943444297997765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49791276628962865331843 74686914943444297997765)
              ·
                refine ⟨14003796551895805874581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74686914943444297997765 14003796551895805874581)
                ·
                  rfl

theorem cell19_46022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_46022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46022 prefixEnd_46022 := by exact prefixLift 46022
  have htrace : WordTrace (prefixWord ++ tailWord_46022) baseStart_46022 baseEnd_46022 := by
    simpa [prefixWord, tailWord_46022, baseEnd_46022] using wordTrace_append hprefix tailTrace_46022
  have hstable : (prefixWord ++ tailWord_46022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46022).length < 2 ^ (prefixWord ++ tailWord_46022).sum := by decide
  have hdescent : baseEnd_46022 < baseStart_46022 := by decide
  rcases family_descends (prefixWord ++ tailWord_46022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46051 : List Nat := [1, 1, 1, 6, 1, 1, 5, 3]
def baseStart_46051 : Nat := 118140960795 + 46051 * 2 ^ 59
def prefixEnd_46051 : Nat := 4983230072969 + 3 ^ 40 * 46051 * 2
def baseEnd_46051 : Nat := 14012620812032331230057

theorem tailTrace_46051 : CollatzResearch.WordTrace tailWord_46051 prefixEnd_46051 14012620812032331230057 := by
  unfold tailWord_46051
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679617956172566729754007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1119745304115044486502671 1679617956172566729754007)
  ·
    refine ⟨2519426934258850094631011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1679617956172566729754007 2519426934258850094631011)
    ·
      refine ⟨3779140401388275141946517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519426934258850094631011 3779140401388275141946517)
      ·
        refine ⟨177147206315075397278743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3779140401388275141946517 177147206315075397278743)
        ·
          refine ⟨265720809472613095918115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177147206315075397278743 265720809472613095918115)
          ·
            refine ⟨398581214208919643877173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265720809472613095918115 398581214208919643877173)
            ·
              refine ⟨37366988832086216613485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398581214208919643877173 37366988832086216613485)
              ·
                refine ⟨14012620812032331230057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37366988832086216613485 14012620812032331230057)
                ·
                  rfl

theorem cell19_46051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_46051 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46051 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46051 prefixEnd_46051 := by exact prefixLift 46051
  have htrace : WordTrace (prefixWord ++ tailWord_46051) baseStart_46051 baseEnd_46051 := by
    simpa [prefixWord, tailWord_46051, baseEnd_46051] using wordTrace_append hprefix tailTrace_46051
  have hstable : (prefixWord ++ tailWord_46051).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46051).length < 2 ^ (prefixWord ++ tailWord_46051).sum := by decide
  have hdescent : baseEnd_46051 < baseStart_46051 := by decide
  rcases family_descends (prefixWord ++ tailWord_46051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46070 : List Nat := [5, 1, 1, 1, 3, 2, 6]
def baseStart_46070 : Nat := 118140960795 + 46070 * 2 ^ 59
def prefixEnd_46070 : Nat := 4983230072969 + 3 ^ 40 * 46070 * 2
def baseEnd_46070 : Nat := 4672800741281972269261

theorem tailTrace_46070 : CollatzResearch.WordTrace tailWord_46070 prefixEnd_46070 4672800741281972269261 := by
  unfold tailWord_46070
  simp only [CollatzResearch.WordTrace]
  refine ⟨105019433943983310918479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1120207295402488649797109 105019433943983310918479)
  ·
    refine ⟨157529150915974966377719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105019433943983310918479 157529150915974966377719)
    ·
      refine ⟨236293726373962449566579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157529150915974966377719 236293726373962449566579)
      ·
        refine ⟨354440589560943674349869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236293726373962449566579 354440589560943674349869)
        ·
          refine ⟨132915221085353877881201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 354440589560943674349869 132915221085353877881201)
          ·
            refine ⟨99686415814015408410901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132915221085353877881201 99686415814015408410901)
            ·
              refine ⟨4672800741281972269261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99686415814015408410901 4672800741281972269261)
              ·
                rfl

theorem cell19_46070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_46070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46070 prefixEnd_46070 := by exact prefixLift 46070
  have htrace : WordTrace (prefixWord ++ tailWord_46070) baseStart_46070 baseEnd_46070 := by
    simpa [prefixWord, tailWord_46070, baseEnd_46070] using wordTrace_append hprefix tailTrace_46070
  have hstable : (prefixWord ++ tailWord_46070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46070).length < 2 ^ (prefixWord ++ tailWord_46070).sum := by decide
  have hdescent : baseEnd_46070 < baseStart_46070 := by decide
  rcases family_descends (prefixWord ++ tailWord_46070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46108 : List Nat := [2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_46108 : Nat := 118140960795 + 46108 * 2 ^ 59
def prefixEnd_46108 : Nat := 4983230072969 + 3 ^ 40 * 46108 * 2
def baseEnd_46108 : Nat := 14029965047473087963235

theorem tailTrace_46108 : CollatzResearch.WordTrace tailWord_46108 prefixEnd_46108 14029965047473087963235 := by
  unfold tailWord_46108
  simp only [CollatzResearch.WordTrace]
  refine ⟨840848458483032732289489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1121131277977376976385985 840848458483032732289489)
  ·
    refine ⟨630636343862274549217117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 840848458483032732289489 630636343862274549217117)
    ·
      refine ⟨236488628948352955956419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 630636343862274549217117 236488628948352955956419)
      ·
        refine ⟨354732943422529433934629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236488628948352955956419 354732943422529433934629)
        ·
          refine ⟨66512426891724268862743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354732943422529433934629 66512426891724268862743)
          ·
            refine ⟨99768640337586403294115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66512426891724268862743 99768640337586403294115)
            ·
              refine ⟨149652960506379604941173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99768640337586403294115 149652960506379604941173)
              ·
                refine ⟨14029965047473087963235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149652960506379604941173 14029965047473087963235)
                ·
                  rfl

theorem cell19_46108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_46108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46108 prefixEnd_46108 := by exact prefixLift 46108
  have htrace : WordTrace (prefixWord ++ tailWord_46108) baseStart_46108 baseEnd_46108 := by
    simpa [prefixWord, tailWord_46108, baseEnd_46108] using wordTrace_append hprefix tailTrace_46108
  have hstable : (prefixWord ++ tailWord_46108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46108).length < 2 ^ (prefixWord ++ tailWord_46108).sum := by decide
  have hdescent : baseEnd_46108 < baseStart_46108 := by decide
  rcases family_descends (prefixWord ++ tailWord_46108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46184 : List Nat := [2, 1, 4, 4, 1, 7]
def baseStart_46184 : Nat := 118140960795 + 46184 * 2 ^ 59
def prefixEnd_46184 : Nat := 4983230072969 + 3 ^ 40 * 46184 * 2
def baseEnd_46184 : Nat := 1561454521636381141571

theorem tailTrace_46184 : CollatzResearch.WordTrace tailWord_46184 prefixEnd_46184 1561454521636381141571 := by
  unfold tailWord_46184
  simp only [CollatzResearch.WordTrace]
  refine ⟨842234432345365222172803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1122979243127153629563737 842234432345365222172803)
  ·
    refine ⟨1263351648518047833259205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 842234432345365222172803 1263351648518047833259205)
    ·
      refine ⟨236878434097133968736101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1263351648518047833259205 236878434097133968736101)
      ·
        refine ⟨44414706393212619138019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236878434097133968736101 44414706393212619138019)
        ·
          refine ⟨66622059589818928707029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44414706393212619138019 66622059589818928707029)
          ·
            refine ⟨1561454521636381141571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 66622059589818928707029 1561454521636381141571)
            ·
              rfl

theorem cell19_46184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 7].length) (baseStart_46184 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46184 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46184 prefixEnd_46184 := by exact prefixLift 46184
  have htrace : WordTrace (prefixWord ++ tailWord_46184) baseStart_46184 baseEnd_46184 := by
    simpa [prefixWord, tailWord_46184, baseEnd_46184] using wordTrace_append hprefix tailTrace_46184
  have hstable : (prefixWord ++ tailWord_46184).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46184).length < 2 ^ (prefixWord ++ tailWord_46184).sum := by decide
  have hdescent : baseEnd_46184 < baseStart_46184 := by decide
  rcases family_descends (prefixWord ++ tailWord_46184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46186 : List Nat := [3, 1, 3, 2, 2, 8]
def baseStart_46186 : Nat := 118140960795 + 46186 * 2 ^ 59
def prefixEnd_46186 : Nat := 4983230072969 + 3 ^ 40 * 46186 * 2
def baseEnd_46186 : Nat := 1561522140488002025521

theorem tailTrace_46186 : CollatzResearch.WordTrace tailWord_46186 prefixEnd_46186 1561522140488002025521 := by
  unfold tailWord_46186
  simp only [CollatzResearch.WordTrace]
  refine ⟨421135452670871196479603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1123027873788989857278941 421135452670871196479603)
  ·
    refine ⟨631703179006306794719405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 421135452670871196479603 631703179006306794719405)
    ·
      refine ⟨236888692127365048019777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 631703179006306794719405 236888692127365048019777)
      ·
        refine ⟨177666519095523786014833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236888692127365048019777 177666519095523786014833)
        ·
          refine ⟨133249889321642839511125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177666519095523786014833 133249889321642839511125)
          ·
            refine ⟨1561522140488002025521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 133249889321642839511125 1561522140488002025521)
            ·
              rfl

theorem cell19_46186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 8].length) (baseStart_46186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46186 prefixEnd_46186 := by exact prefixLift 46186
  have htrace : WordTrace (prefixWord ++ tailWord_46186) baseStart_46186 baseEnd_46186 := by
    simpa [prefixWord, tailWord_46186, baseEnd_46186] using wordTrace_append hprefix tailTrace_46186
  have hstable : (prefixWord ++ tailWord_46186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46186).length < 2 ^ (prefixWord ++ tailWord_46186).sum := by decide
  have hdescent : baseEnd_46186 < baseStart_46186 := by decide
  rcases family_descends (prefixWord ++ tailWord_46186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46201 : List Nat := [1, 2, 1, 3, 6, 1, 1, 4]
def baseStart_46201 : Nat := 118140960795 + 46201 * 2 ^ 59
def prefixEnd_46201 : Nat := 4983230072969 + 3 ^ 40 * 46201 * 2
def baseEnd_46201 : Nat := 14058263536876427896315

theorem tailTrace_46201 : CollatzResearch.WordTrace tailWord_46201 prefixEnd_46201 14058263536876427896315 := by
  unfold tailWord_46201
  simp only [CollatzResearch.WordTrace]
  refine ⟨1685088905629142347714457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1123392603752761565142971 1685088905629142347714457)
  ·
    refine ⟨1263816679221856760785843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1685088905629142347714457 1263816679221856760785843)
    ·
      refine ⟨1895725018832785141178765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1263816679221856760785843 1895725018832785141178765)
      ·
        refine ⟨710896882062294427942037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1895725018832785141178765 710896882062294427942037)
        ·
          refine ⟨33323291346670051309783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 710896882062294427942037 33323291346670051309783)
          ·
            refine ⟨49984937020005076964675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33323291346670051309783 49984937020005076964675)
            ·
              refine ⟨74977405530007615447013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49984937020005076964675 74977405530007615447013)
              ·
                refine ⟨14058263536876427896315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74977405530007615447013 14058263536876427896315)
                ·
                  rfl

theorem cell19_46201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 4].length) (baseStart_46201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46201 prefixEnd_46201 := by exact prefixLift 46201
  have htrace : WordTrace (prefixWord ++ tailWord_46201) baseStart_46201 baseEnd_46201 := by
    simpa [prefixWord, tailWord_46201, baseEnd_46201] using wordTrace_append hprefix tailTrace_46201
  have hstable : (prefixWord ++ tailWord_46201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46201).length < 2 ^ (prefixWord ++ tailWord_46201).sum := by decide
  have hdescent : baseEnd_46201 < baseStart_46201 := by decide
  rcases family_descends (prefixWord ++ tailWord_46201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46294 : List Nat := [5, 2, 1, 2, 3, 1, 5]
def baseStart_46294 : Nat := 118140960795 + 46294 * 2 ^ 59
def prefixEnd_46294 : Nat := 4983230072969 + 3 ^ 40 * 46294 * 2
def baseEnd_46294 : Nat := 4695520675426589276465

theorem tailTrace_46294 : CollatzResearch.WordTrace tailWord_46294 prefixEnd_46294 4695520675426589276465 := by
  unfold tailWord_46294
  simp only [CollatzResearch.WordTrace]
  refine ⟨105530055893263701928121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1125653929528146153899957 105530055893263701928121)
  ·
    refine ⟨79147541919947776446091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105530055893263701928121 79147541919947776446091)
    ·
      refine ⟨118721312879921664669137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79147541919947776446091 118721312879921664669137)
      ·
        refine ⟨89040984659941248501853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118721312879921664669137 89040984659941248501853)
        ·
          refine ⟨33390369247477968188195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89040984659941248501853 33390369247477968188195)
          ·
            refine ⟨50085553871216952282293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33390369247477968188195 50085553871216952282293)
            ·
              refine ⟨4695520675426589276465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50085553871216952282293 4695520675426589276465)
              ·
                rfl

theorem cell19_46294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 5].length) (baseStart_46294 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46294 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46294 prefixEnd_46294 := by exact prefixLift 46294
  have htrace : WordTrace (prefixWord ++ tailWord_46294) baseStart_46294 baseEnd_46294 := by
    simpa [prefixWord, tailWord_46294, baseEnd_46294] using wordTrace_append hprefix tailTrace_46294
  have hstable : (prefixWord ++ tailWord_46294).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46294).length < 2 ^ (prefixWord ++ tailWord_46294).sum := by decide
  have hdescent : baseEnd_46294 < baseStart_46294 := by decide
  rcases family_descends (prefixWord ++ tailWord_46294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46317 : List Nat := [1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_46317 : Nat := 118140960795 + 46317 * 2 ^ 59
def prefixEnd_46317 : Nat := 4983230072969 + 3 ^ 40 * 46317 * 2
def baseEnd_46317 : Nat := 14093560577422529318221

theorem tailTrace_46317 : CollatzResearch.WordTrace tailWord_46317 prefixEnd_46317 14093560577422529318221 := by
  unfold tailWord_46317
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689319773208894158937205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1126213182139262772624803 1689319773208894158937205)
  ·
    refine ⟨158373728738333827400363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1689319773208894158937205 158373728738333827400363)
    ·
      refine ⟨237560593107500741100545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158373728738333827400363 237560593107500741100545)
      ·
        refine ⟨178170444830625555825409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237560593107500741100545 178170444830625555825409)
        ·
          refine ⟨133627833622969166869057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178170444830625555825409 133627833622969166869057)
          ·
            refine ⟨100220875217226875151793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133627833622969166869057 100220875217226875151793)
            ·
              refine ⟨75165656412920156363845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100220875217226875151793 75165656412920156363845)
              ·
                refine ⟨14093560577422529318221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75165656412920156363845 14093560577422529318221)
                ·
                  rfl

theorem cell19_46317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_46317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46317 prefixEnd_46317 := by exact prefixLift 46317
  have htrace : WordTrace (prefixWord ++ tailWord_46317) baseStart_46317 baseEnd_46317 := by
    simpa [prefixWord, tailWord_46317, baseEnd_46317] using wordTrace_append hprefix tailTrace_46317
  have hstable : (prefixWord ++ tailWord_46317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46317).length < 2 ^ (prefixWord ++ tailWord_46317).sum := by decide
  have hdescent : baseEnd_46317 < baseStart_46317 := by decide
  rcases family_descends (prefixWord ++ tailWord_46317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46416 : List Nat := [2, 1, 1, 1, 1, 5, 8]
def baseStart_46416 : Nat := 118140960795 + 46416 * 2 ^ 59
def prefixEnd_46416 : Nat := 4983230072969 + 3 ^ 40 * 46416 * 2
def baseEnd_46416 : Nat := 4707894925273211039317

theorem tailTrace_46416 : CollatzResearch.WordTrace tailWord_46416 prefixEnd_46416 4707894925273211039317 := by
  unfold tailWord_46416
  simp only [CollatzResearch.WordTrace]
  refine ⟨846465299925117033395551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1128620399900156044527401 846465299925117033395551)
  ·
    refine ⟨1269697949887675550093327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 846465299925117033395551 1269697949887675550093327)
    ·
      refine ⟨1904546924831513325139991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269697949887675550093327 1904546924831513325139991)
      ·
        refine ⟨2856820387247269987709987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904546924831513325139991 2856820387247269987709987)
        ·
          refine ⟨4285230580870904981564981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856820387247269987709987 4285230580870904981564981)
          ·
            refine ⟨401740366956647342021717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4285230580870904981564981 401740366956647342021717)
            ·
              refine ⟨4707894925273211039317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 401740366956647342021717 4707894925273211039317)
              ·
                rfl

theorem cell19_46416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_46416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46416 prefixEnd_46416 := by exact prefixLift 46416
  have htrace : WordTrace (prefixWord ++ tailWord_46416) baseStart_46416 baseEnd_46416 := by
    simpa [prefixWord, tailWord_46416, baseEnd_46416] using wordTrace_append hprefix tailTrace_46416
  have hstable : (prefixWord ++ tailWord_46416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46416).length < 2 ^ (prefixWord ++ tailWord_46416).sum := by decide
  have hdescent : baseEnd_46416 < baseStart_46416 := by decide
  rcases family_descends (prefixWord ++ tailWord_46416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46446 : List Nat := [4, 1, 2, 4, 1, 2, 2, 3]
def baseStart_46446 : Nat := 118140960795 + 46446 * 2 ^ 59
def prefixEnd_46446 : Nat := 4983230072969 + 3 ^ 40 * 46446 * 2
def baseEnd_46446 : Nat := 14132813320788452451203

theorem tailTrace_46446 : CollatzResearch.WordTrace tailWord_46446 prefixEnd_46446 14132813320788452451203 := by
  unfold tailWord_46446
  simp only [CollatzResearch.WordTrace]
  refine ⟨211753098717693648797899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1129349859827699460255461 211753098717693648797899)
  ·
    refine ⟨317629648076540473196849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211753098717693648797899 317629648076540473196849)
    ·
      refine ⟨238222236057405354897637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317629648076540473196849 238222236057405354897637)
      ·
        refine ⟨44666669260763504043307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238222236057405354897637 44666669260763504043307)
        ·
          refine ⟨67000003891145256064961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44666669260763504043307 67000003891145256064961)
          ·
            refine ⟨50250002918358942048721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67000003891145256064961 50250002918358942048721)
            ·
              refine ⟨37687502188769206536541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50250002918358942048721 37687502188769206536541)
              ·
                refine ⟨14132813320788452451203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37687502188769206536541 14132813320788452451203)
                ·
                  rfl

theorem cell19_46446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_46446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46446 prefixEnd_46446 := by exact prefixLift 46446
  have htrace : WordTrace (prefixWord ++ tailWord_46446) baseStart_46446 baseEnd_46446 := by
    simpa [prefixWord, tailWord_46446, baseEnd_46446] using wordTrace_append hprefix tailTrace_46446
  have hstable : (prefixWord ++ tailWord_46446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46446).length < 2 ^ (prefixWord ++ tailWord_46446).sum := by decide
  have hdescent : baseEnd_46446 < baseStart_46446 := by decide
  rcases family_descends (prefixWord ++ tailWord_46446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46471 : List Nat := [1, 1, 4, 2, 2, 4, 5]
def baseStart_46471 : Nat := 118140960795 + 46471 * 2 ^ 59
def prefixEnd_46471 : Nat := 4983230072969 + 3 ^ 40 * 46471 * 2
def baseEnd_46471 : Nat := 4713473480531933965193

theorem tailTrace_46471 : CollatzResearch.WordTrace tailWord_46471 prefixEnd_46471 4713473480531933965193 := by
  unfold tailWord_46471
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694936614650978460043267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1129957743100652306695511 1694936614650978460043267)
  ·
    refine ⟨2542404921976467690064901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1694936614650978460043267 2542404921976467690064901)
    ·
      refine ⟨476700922870587691887169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2542404921976467690064901 476700922870587691887169)
      ·
        refine ⟨357525692152940768915377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476700922870587691887169 357525692152940768915377)
        ·
          refine ⟨268144269114705576686533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357525692152940768915377 268144269114705576686533)
          ·
            refine ⟨50277050459007295628725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268144269114705576686533 50277050459007295628725)
            ·
              refine ⟨4713473480531933965193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50277050459007295628725 4713473480531933965193)
              ·
                rfl

theorem cell19_46471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_46471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46471 prefixEnd_46471 := by exact prefixLift 46471
  have htrace : WordTrace (prefixWord ++ tailWord_46471) baseStart_46471 baseEnd_46471 := by
    simpa [prefixWord, tailWord_46471, baseEnd_46471] using wordTrace_append hprefix tailTrace_46471
  have hstable : (prefixWord ++ tailWord_46471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46471).length < 2 ^ (prefixWord ++ tailWord_46471).sum := by decide
  have hdescent : baseEnd_46471 < baseStart_46471 := by decide
  rcases family_descends (prefixWord ++ tailWord_46471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46488 : List Nat := [2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_46488 : Nat := 118140960795 + 46488 * 2 ^ 59
def prefixEnd_46488 : Nat := 4983230072969 + 3 ^ 40 * 46488 * 2
def baseEnd_46488 : Nat := 14145593283744799517755

theorem tailTrace_46488 : CollatzResearch.WordTrace tailWord_46488 prefixEnd_46488 14145593283744799517755 := by
  unfold tailWord_46488
  simp only [CollatzResearch.WordTrace]
  refine ⟨847778327794695181706059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1130371103726260242274745 847778327794695181706059)
  ·
    refine ⟨1271667491692042772559089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 847778327794695181706059 1271667491692042772559089)
    ·
      refine ⟨953750618769032079419317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1271667491692042772559089 953750618769032079419317)
      ·
        refine ⟨89414120509596757445561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 953750618769032079419317 89414120509596757445561)
        ·
          refine ⟨67060590382197568084171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89414120509596757445561 67060590382197568084171)
          ·
            refine ⟨100590885573296352126257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67060590382197568084171 100590885573296352126257)
            ·
              refine ⟨75443164179972264094693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100590885573296352126257 75443164179972264094693)
              ·
                refine ⟨14145593283744799517755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75443164179972264094693 14145593283744799517755)
                ·
                  rfl

theorem cell19_46488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_46488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46488 prefixEnd_46488 := by exact prefixLift 46488
  have htrace : WordTrace (prefixWord ++ tailWord_46488) baseStart_46488 baseEnd_46488 := by
    simpa [prefixWord, tailWord_46488, baseEnd_46488] using wordTrace_append hprefix tailTrace_46488
  have hstable : (prefixWord ++ tailWord_46488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46488).length < 2 ^ (prefixWord ++ tailWord_46488).sum := by decide
  have hdescent : baseEnd_46488 < baseStart_46488 := by decide
  rcases family_descends (prefixWord ++ tailWord_46488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46490 : List Nat := [3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_46490 : Nat := 118140960795 + 46490 * 2 ^ 59
def prefixEnd_46490 : Nat := 4983230072969 + 3 ^ 40 * 46490 * 2
def baseEnd_46490 : Nat := 14146201853409387473305

theorem tailTrace_46490 : CollatzResearch.WordTrace tailWord_46490 prefixEnd_46490 14146201853409387473305 := by
  unfold tailWord_46490
  simp only [CollatzResearch.WordTrace]
  refine ⟨423907400395536176246231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1130419734388096469989949 423907400395536176246231)
  ·
    refine ⟨635861100593304264369347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 423907400395536176246231 635861100593304264369347)
    ·
      refine ⟨953791650889956396554021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635861100593304264369347 953791650889956396554021)
      ·
        refine ⟨178835934541866824353879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 953791650889956396554021 178835934541866824353879)
        ·
          refine ⟨268253901812800236530819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178835934541866824353879 268253901812800236530819)
          ·
            refine ⟨402380852719200354796229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268253901812800236530819 402380852719200354796229)
            ·
              refine ⟨75446409884850066524293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 402380852719200354796229 75446409884850066524293)
              ·
                refine ⟨14146201853409387473305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75446409884850066524293 14146201853409387473305)
                ·
                  rfl

theorem cell19_46490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_46490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46490 prefixEnd_46490 := by exact prefixLift 46490
  have htrace : WordTrace (prefixWord ++ tailWord_46490) baseStart_46490 baseEnd_46490 := by
    simpa [prefixWord, tailWord_46490, baseEnd_46490] using wordTrace_append hprefix tailTrace_46490
  have hstable : (prefixWord ++ tailWord_46490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46490).length < 2 ^ (prefixWord ++ tailWord_46490).sum := by decide
  have hdescent : baseEnd_46490 < baseStart_46490 := by decide
  rcases family_descends (prefixWord ++ tailWord_46490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46623 : List Nat := [1, 1, 2, 4, 1, 1, 6, 3]
def baseStart_46623 : Nat := 118140960795 + 46623 * 2 ^ 59
def prefixEnd_46623 : Nat := 4983230072969 + 3 ^ 40 * 46623 * 2
def baseEnd_46623 : Nat := 14186671736104486517387

theorem tailTrace_46623 : CollatzResearch.WordTrace tailWord_46623 prefixEnd_46623 14186671736104486517387 := by
  unfold tailWord_46623
  simp only [CollatzResearch.WordTrace]
  refine ⟨1700480510100308419576523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1133653673400205613051015 1700480510100308419576523)
  ·
    refine ⟨2550720765150462629364785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1700480510100308419576523 2550720765150462629364785)
    ·
      refine ⟨1913040573862846972023589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2550720765150462629364785 1913040573862846972023589)
      ·
        refine ⟨358695107599283807254423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1913040573862846972023589 358695107599283807254423)
        ·
          refine ⟨538042661398925710881635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358695107599283807254423 538042661398925710881635)
          ·
            refine ⟨807063992098388566322453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538042661398925710881635 807063992098388566322453)
            ·
              refine ⟨37831124629611964046365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 807063992098388566322453 37831124629611964046365)
              ·
                refine ⟨14186671736104486517387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37831124629611964046365 14186671736104486517387)
                ·
                  rfl

theorem cell19_46623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_46623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46623 prefixEnd_46623 := by exact prefixLift 46623
  have htrace : WordTrace (prefixWord ++ tailWord_46623) baseStart_46623 baseEnd_46623 := by
    simpa [prefixWord, tailWord_46623, baseEnd_46623] using wordTrace_append hprefix tailTrace_46623
  have hstable : (prefixWord ++ tailWord_46623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46623).length < 2 ^ (prefixWord ++ tailWord_46623).sum := by decide
  have hdescent : baseEnd_46623 < baseStart_46623 := by decide
  rcases family_descends (prefixWord ++ tailWord_46623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46701 : List Nat := [1, 5, 1, 1, 11]
def baseStart_46701 : Nat := 118140960795 + 46701 * 2 ^ 59
def prefixEnd_46701 : Nat := 4983230072969 + 3 ^ 40 * 46701 * 2
def baseEnd_46701 : Nat := 526311331593459880883

theorem tailTrace_46701 : CollatzResearch.WordTrace tailWord_46701 prefixEnd_46701 526311331593459880883 := by
  unfold tailWord_46701
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703325403817727740915957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1135550269211818493943971 1703325403817727740915957)
  ·
    refine ⟨159686756607911975710871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1703325403817727740915957 159686756607911975710871)
    ·
      refine ⟨239530134911867963566307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159686756607911975710871 239530134911867963566307)
      ·
        refine ⟨359295202367801945349461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239530134911867963566307 359295202367801945349461)
        ·
          refine ⟨526311331593459880883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 359295202367801945349461 526311331593459880883)
          ·
            rfl

theorem cell19_46701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 11].length) (baseStart_46701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46701 prefixEnd_46701 := by exact prefixLift 46701
  have htrace : WordTrace (prefixWord ++ tailWord_46701) baseStart_46701 baseEnd_46701 := by
    simpa [prefixWord, tailWord_46701, baseEnd_46701] using wordTrace_append hprefix tailTrace_46701
  have hstable : (prefixWord ++ tailWord_46701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46701).length < 2 ^ (prefixWord ++ tailWord_46701).sum := by decide
  have hdescent : baseEnd_46701 < baseStart_46701 := by decide
  rcases family_descends (prefixWord ++ tailWord_46701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46754 : List Nat := [3, 3, 1, 4, 1, 1, 6]
def baseStart_46754 : Nat := 118140960795 + 46754 * 2 ^ 59
def prefixEnd_46754 : Nat := 4983230072969 + 3 ^ 40 * 46754 * 2
def baseEnd_46754 : Nat := 4742177683044999201973

theorem tailTrace_46754 : CollatzResearch.WordTrace tailWord_46754 prefixEnd_46754 4742177683044999201973 := by
  unfold tailWord_46754
  simp only [CollatzResearch.WordTrace]
  refine ⟨426314618156429448148829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1136838981750478528396877 426314618156429448148829)
  ·
    refine ⟨159867981808661043055811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 426314618156429448148829 159867981808661043055811)
    ·
      refine ⟨239801972712991564583717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159867981808661043055811 239801972712991564583717)
      ·
        refine ⟨44962869883685918359447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239801972712991564583717 44962869883685918359447)
        ·
          refine ⟨67444304825528877539171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44962869883685918359447 67444304825528877539171)
          ·
            refine ⟨101166457238293316308757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67444304825528877539171 101166457238293316308757)
            ·
              refine ⟨4742177683044999201973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101166457238293316308757 4742177683044999201973)
              ·
                rfl

theorem cell19_46754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_46754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46754 prefixEnd_46754 := by exact prefixLift 46754
  have htrace : WordTrace (prefixWord ++ tailWord_46754) baseStart_46754 baseEnd_46754 := by
    simpa [prefixWord, tailWord_46754, baseEnd_46754] using wordTrace_append hprefix tailTrace_46754
  have hstable : (prefixWord ++ tailWord_46754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46754).length < 2 ^ (prefixWord ++ tailWord_46754).sum := by decide
  have hdescent : baseEnd_46754 < baseStart_46754 := by decide
  rcases family_descends (prefixWord ++ tailWord_46754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46786 : List Nat := [3, 5, 1, 2, 1, 2, 2, 3]
def baseStart_46786 : Nat := 118140960795 + 46786 * 2 ^ 59
def prefixEnd_46786 : Nat := 4983230072969 + 3 ^ 40 * 46786 * 2
def baseEnd_46786 : Nat := 14236270163768404894721

theorem tailTrace_46786 : CollatzResearch.WordTrace tailWord_46786 prefixEnd_46786 14236270163768404894721 := by
  unfold tailWord_46786
  simp only [CollatzResearch.WordTrace]
  refine ⟨426606402127446814440053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1137617072339858171840141 426606402127446814440053)
  ·
    refine ⟨39994350199448138853755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 426606402127446814440053 39994350199448138853755)
    ·
      refine ⟨59991525299172208280633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39994350199448138853755 59991525299172208280633)
      ·
        refine ⟨44993643974379156210475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59991525299172208280633 44993643974379156210475)
        ·
          refine ⟨67490465961568734315713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44993643974379156210475 67490465961568734315713)
          ·
            refine ⟨50617849471176550736785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67490465961568734315713 50617849471176550736785)
            ·
              refine ⟨37963387103382413052589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50617849471176550736785 37963387103382413052589)
              ·
                refine ⟨14236270163768404894721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37963387103382413052589 14236270163768404894721)
                ·
                  rfl

theorem cell19_46786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_46786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46786 prefixEnd_46786 := by exact prefixLift 46786
  have htrace : WordTrace (prefixWord ++ tailWord_46786) baseStart_46786 baseEnd_46786 := by
    simpa [prefixWord, tailWord_46786, baseEnd_46786] using wordTrace_append hprefix tailTrace_46786
  have hstable : (prefixWord ++ tailWord_46786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46786).length < 2 ^ (prefixWord ++ tailWord_46786).sum := by decide
  have hdescent : baseEnd_46786 < baseStart_46786 := by decide
  rcases family_descends (prefixWord ++ tailWord_46786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46790 : List Nat := [6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_46790 : Nat := 118140960795 + 46790 * 2 ^ 59
def prefixEnd_46790 : Nat := 4983230072969 + 3 ^ 40 * 46790 * 2
def baseEnd_46790 : Nat := 14237487303097580805821

theorem tailTrace_46790 : CollatzResearch.WordTrace tailWord_46790 prefixEnd_46790 14237487303097580805821 := by
  unfold tailWord_46790
  simp only [CollatzResearch.WordTrace]
  refine ⟨53330359390477998153307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1137714333663530627270549 53330359390477998153307)
  ·
    refine ⟨79995539085716997229961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53330359390477998153307 79995539085716997229961)
    ·
      refine ⟨59996654314287747922471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79995539085716997229961 59996654314287747922471)
      ·
        refine ⟨89994981471431621883707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59996654314287747922471 89994981471431621883707)
        ·
          refine ⟨134992472207147432825561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89994981471431621883707 134992472207147432825561)
          ·
            refine ⟨101244354155360574619171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134992472207147432825561 101244354155360574619171)
            ·
              refine ⟨151866531233040861928757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101244354155360574619171 151866531233040861928757)
              ·
                refine ⟨14237487303097580805821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151866531233040861928757 14237487303097580805821)
                ·
                  rfl

theorem cell19_46790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_46790 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46790 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46790 prefixEnd_46790 := by exact prefixLift 46790
  have htrace : WordTrace (prefixWord ++ tailWord_46790) baseStart_46790 baseEnd_46790 := by
    simpa [prefixWord, tailWord_46790, baseEnd_46790] using wordTrace_append hprefix tailTrace_46790
  have hstable : (prefixWord ++ tailWord_46790).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46790).length < 2 ^ (prefixWord ++ tailWord_46790).sum := by decide
  have hdescent : baseEnd_46790 < baseStart_46790 := by decide
  rcases family_descends (prefixWord ++ tailWord_46790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46794 : List Nat := [3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_46794 : Nat := 118140960795 + 46794 * 2 ^ 59
def prefixEnd_46794 : Nat := 4983230072969 + 3 ^ 40 * 46794 * 2
def baseEnd_46794 : Nat := 14238704442426756716921

theorem tailTrace_46794 : CollatzResearch.WordTrace tailWord_46794 prefixEnd_46794 14238704442426756716921 := by
  unfold tailWord_46794
  simp only [CollatzResearch.WordTrace]
  refine ⟨426679348120201156012859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1137811594987203082700957 426679348120201156012859)
  ·
    refine ⟨640019022180301734019289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426679348120201156012859 640019022180301734019289)
    ·
      refine ⟨480014266635226300514467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 640019022180301734019289 480014266635226300514467)
      ·
        refine ⟨720021399952839450771701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480014266635226300514467 720021399952839450771701)
        ·
          refine ⟨67502006245578698509847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 720021399952839450771701 67502006245578698509847)
          ·
            refine ⟨101253009368368047764771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67502006245578698509847 101253009368368047764771)
            ·
              refine ⟨151879514052552071647157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101253009368368047764771 151879514052552071647157)
              ·
                refine ⟨14238704442426756716921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 151879514052552071647157 14238704442426756716921)
                ·
                  rfl

theorem cell19_46794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_46794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46794 prefixEnd_46794 := by exact prefixLift 46794
  have htrace : WordTrace (prefixWord ++ tailWord_46794) baseStart_46794 baseEnd_46794 := by
    simpa [prefixWord, tailWord_46794, baseEnd_46794] using wordTrace_append hprefix tailTrace_46794
  have hstable : (prefixWord ++ tailWord_46794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46794).length < 2 ^ (prefixWord ++ tailWord_46794).sum := by decide
  have hdescent : baseEnd_46794 < baseStart_46794 := by decide
  rcases family_descends (prefixWord ++ tailWord_46794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46868 : List Nat := [2, 4, 4, 1, 8]
def baseStart_46868 : Nat := 118140960795 + 46868 * 2 ^ 59
def prefixEnd_46868 : Nat := 4983230072969 + 3 ^ 40 * 46868 * 2
def baseEnd_46868 : Nat := 528193389630241150825

theorem tailTrace_46868 : CollatzResearch.WordTrace tailWord_46868 prefixEnd_46868 528193389630241150825 := by
  unfold tailWord_46868
  simp only [CollatzResearch.WordTrace]
  refine ⟨854708197106357631122629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1139610929475143508163505 854708197106357631122629)
  ·
    refine ⟨160257786957442055835493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 854708197106357631122629 160257786957442055835493)
    ·
      refine ⟨30048335054520385469155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160257786957442055835493 30048335054520385469155)
      ·
        refine ⟨45072502581780578203733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30048335054520385469155 45072502581780578203733)
        ·
          refine ⟨528193389630241150825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 45072502581780578203733 528193389630241150825)
          ·
            rfl

theorem cell19_46868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 8].length) (baseStart_46868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46868 prefixEnd_46868 := by exact prefixLift 46868
  have htrace : WordTrace (prefixWord ++ tailWord_46868) baseStart_46868 baseEnd_46868 := by
    simpa [prefixWord, tailWord_46868, baseEnd_46868] using wordTrace_append hprefix tailTrace_46868
  have hstable : (prefixWord ++ tailWord_46868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46868).length < 2 ^ (prefixWord ++ tailWord_46868).sum := by decide
  have hdescent : baseEnd_46868 < baseStart_46868 := by decide
  rcases family_descends (prefixWord ++ tailWord_46868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46929 : List Nat := [1, 2, 2, 1, 5, 2, 6]
def baseStart_46929 : Nat := 118140960795 + 46929 * 2 ^ 59
def prefixEnd_46929 : Nat := 4983230072969 + 3 ^ 40 * 46929 * 2
def baseEnd_46929 : Nat := 4759927631595481238851

theorem tailTrace_46929 : CollatzResearch.WordTrace tailWord_46929 prefixEnd_46929 4759927631595481238851 := by
  unfold tailWord_46929
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711641246991722680215841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1141094164661148453477227 1711641246991722680215841)
  ·
    refine ⟨1283730935243792010161881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1711641246991722680215841 1283730935243792010161881)
    ·
      refine ⟨962798201432844007621411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1283730935243792010161881 962798201432844007621411)
      ·
        refine ⟨1444197302149266011432117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962798201432844007621411 1444197302149266011432117)
        ·
          refine ⟨135393497076493688571761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1444197302149266011432117 135393497076493688571761)
          ·
            refine ⟨101545122807370266428821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135393497076493688571761 101545122807370266428821)
            ·
              refine ⟨4759927631595481238851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101545122807370266428821 4759927631595481238851)
              ·
                rfl

theorem cell19_46929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_46929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46929 prefixEnd_46929 := by exact prefixLift 46929
  have htrace : WordTrace (prefixWord ++ tailWord_46929) baseStart_46929 baseEnd_46929 := by
    simpa [prefixWord, tailWord_46929, baseEnd_46929] using wordTrace_append hprefix tailTrace_46929
  have hstable : (prefixWord ++ tailWord_46929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46929).length < 2 ^ (prefixWord ++ tailWord_46929).sum := by decide
  have hdescent : baseEnd_46929 < baseStart_46929 := by decide
  rcases family_descends (prefixWord ++ tailWord_46929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46984 : List Nat := [2, 1, 3, 3, 3, 2, 5]
def baseStart_46984 : Nat := 118140960795 + 46984 * 2 ^ 59
def prefixEnd_46984 : Nat := 4983230072969 + 3 ^ 40 * 46984 * 2
def baseEnd_46984 : Nat := 4765506186854204164727

theorem tailTrace_46984 : CollatzResearch.WordTrace tailWord_46984 prefixEnd_46984 4765506186854204164727 := by
  unfold tailWord_46984
  simp only [CollatzResearch.WordTrace]
  refine ⟨856823630896233536734003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1142431507861644715645337 856823630896233536734003)
  ·
    refine ⟨1285235446344350305101005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 856823630896233536734003 1285235446344350305101005)
    ·
      refine ⟨481963292379131364412877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1285235446344350305101005 481963292379131364412877)
      ·
        refine ⟨180736234642174261654829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 481963292379131364412877 180736234642174261654829)
        ·
          refine ⟨67776087990815348120561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180736234642174261654829 67776087990815348120561)
          ·
            refine ⟨50832065993111511090421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67776087990815348120561 50832065993111511090421)
            ·
              refine ⟨4765506186854204164727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50832065993111511090421 4765506186854204164727)
              ·
                rfl

theorem cell19_46984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_46984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_46984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_46984 prefixEnd_46984 := by exact prefixLift 46984
  have htrace : WordTrace (prefixWord ++ tailWord_46984) baseStart_46984 baseEnd_46984 := by
    simpa [prefixWord, tailWord_46984, baseEnd_46984] using wordTrace_append hprefix tailTrace_46984
  have hstable : (prefixWord ++ tailWord_46984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46984).length < 2 ^ (prefixWord ++ tailWord_46984).sum := by decide
  have hdescent : baseEnd_46984 < baseStart_46984 := by decide
  rcases family_descends (prefixWord ++ tailWord_46984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47005 : List Nat := [1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_47005 : Nat := 118140960795 + 47005 * 2 ^ 59
def prefixEnd_47005 : Nat := 4983230072969 + 3 ^ 40 * 47005 * 2
def baseEnd_47005 : Nat := 14302908542040786027457

theorem tailTrace_47005 : CollatzResearch.WordTrace tailWord_47005 prefixEnd_47005 14302908542040786027457 := by
  unfold tailWord_47005
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714413194716387659982469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1142942129810925106654979 1714413194716387659982469)
  ·
    refine ⟨321452474009322686246713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1714413194716387659982469 321452474009322686246713)
    ·
      refine ⟨241089355506992014685035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321452474009322686246713 241089355506992014685035)
      ·
        refine ⟨361634033260488022027553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241089355506992014685035 361634033260488022027553)
        ·
          refine ⟨271225524945366016520665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361634033260488022027553 271225524945366016520665)
          ·
            refine ⟨203419143709024512390499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271225524945366016520665 203419143709024512390499)
            ·
              refine ⟨305128715563536768585749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203419143709024512390499 305128715563536768585749)
              ·
                refine ⟨14302908542040786027457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 305128715563536768585749 14302908542040786027457)
                ·
                  rfl

theorem cell19_47005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_47005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47005 prefixEnd_47005 := by exact prefixLift 47005
  have htrace : WordTrace (prefixWord ++ tailWord_47005) baseStart_47005 baseEnd_47005 := by
    simpa [prefixWord, tailWord_47005, baseEnd_47005] using wordTrace_append hprefix tailTrace_47005
  have hstable : (prefixWord ++ tailWord_47005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47005).length < 2 ^ (prefixWord ++ tailWord_47005).sum := by decide
  have hdescent : baseEnd_47005 < baseStart_47005 := by decide
  rcases family_descends (prefixWord ++ tailWord_47005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47058 : List Nat := [3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_47058 : Nat := 118140960795 + 47058 * 2 ^ 59
def prefixEnd_47058 : Nat := 4983230072969 + 3 ^ 40 * 47058 * 2
def baseEnd_47058 : Nat := 14319035638152366849535

theorem tailTrace_47058 : CollatzResearch.WordTrace tailWord_47058 prefixEnd_47058 14319035638152366849535 := by
  unfold tailWord_47058
  simp only [CollatzResearch.WordTrace]
  refine ⟨429086565881094427915457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1144230842349585141107885 429086565881094427915457)
  ·
    refine ⟨321814924410820820936593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 429086565881094427915457 321814924410820820936593)
    ·
      refine ⟨241361193308115615702445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321814924410820820936593 241361193308115615702445)
      ·
        refine ⟨90510447490543355888417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241361193308115615702445 90510447490543355888417)
        ·
          refine ⟨67882835617907516916313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90510447490543355888417 67882835617907516916313)
          ·
            refine ⟨50912126713430637687235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67882835617907516916313 50912126713430637687235)
            ·
              refine ⟨76368190070145956530853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50912126713430637687235 76368190070145956530853)
              ·
                refine ⟨14319035638152366849535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76368190070145956530853 14319035638152366849535)
                ·
                  rfl

theorem cell19_47058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_47058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47058 prefixEnd_47058 := by exact prefixLift 47058
  have htrace : WordTrace (prefixWord ++ tailWord_47058) baseStart_47058 baseEnd_47058 := by
    simpa [prefixWord, tailWord_47058, baseEnd_47058] using wordTrace_append hprefix tailTrace_47058
  have hstable : (prefixWord ++ tailWord_47058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47058).length < 2 ^ (prefixWord ++ tailWord_47058).sum := by decide
  have hdescent : baseEnd_47058 < baseStart_47058 := by decide
  rcases family_descends (prefixWord ++ tailWord_47058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47083 : List Nat := [1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_47083 : Nat := 118140960795 + 47083 * 2 ^ 59
def prefixEnd_47083 : Nat := 4983230072969 + 3 ^ 40 * 47083 * 2
def baseEnd_47083 : Nat := 14326642758959716293911

theorem tailTrace_47083 : CollatzResearch.WordTrace tailWord_47083 prefixEnd_47083 14326642758959716293911 := by
  unfold tailWord_47083
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717258088433806981321903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1144838725622537987547935 1717258088433806981321903)
  ·
    refine ⟨2575887132650710471982855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1717258088433806981321903 2575887132650710471982855)
    ·
      refine ⟨3863830698976065707974283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2575887132650710471982855 3863830698976065707974283)
      ·
        refine ⟨5795746048464098561961425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3863830698976065707974283 5795746048464098561961425)
        ·
          refine ⟨4346809536348073921471069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5795746048464098561961425 4346809536348073921471069)
          ·
            refine ⟨1630053576130527720551651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4346809536348073921471069 1630053576130527720551651)
            ·
              refine ⟨2445080364195791580827477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1630053576130527720551651 2445080364195791580827477)
              ·
                refine ⟨14326642758959716293911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2445080364195791580827477 14326642758959716293911)
                ·
                  rfl

theorem cell19_47083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_47083 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47083 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47083 prefixEnd_47083 := by exact prefixLift 47083
  have htrace : WordTrace (prefixWord ++ tailWord_47083) baseStart_47083 baseEnd_47083 := by
    simpa [prefixWord, tailWord_47083, baseEnd_47083] using wordTrace_append hprefix tailTrace_47083
  have hstable : (prefixWord ++ tailWord_47083).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47083).length < 2 ^ (prefixWord ++ tailWord_47083).sum := by decide
  have hdescent : baseEnd_47083 < baseStart_47083 := by decide
  rcases family_descends (prefixWord ++ tailWord_47083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47138 : List Nat := [3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_47138 : Nat := 118140960795 + 47138 * 2 ^ 59
def prefixEnd_47138 : Nat := 4983230072969 + 3 ^ 40 * 47138 * 2
def baseEnd_47138 : Nat := 14343378424735885071539

theorem tailTrace_47138 : CollatzResearch.WordTrace tailWord_47138 prefixEnd_47138 14343378424735885071539 := by
  unfold tailWord_47138
  simp only [CollatzResearch.WordTrace]
  refine ⟨429816025808637843643517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1146176068823034249716045 429816025808637843643517)
  ·
    refine ⟨161181009678239191366319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 429816025808637843643517 161181009678239191366319)
    ·
      refine ⟨241771514517358787049479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161181009678239191366319 241771514517358787049479)
      ·
        refine ⟨362657271776038180574219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241771514517358787049479 362657271776038180574219)
        ·
          refine ⟨543985907664057270861329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362657271776038180574219 543985907664057270861329)
          ·
            refine ⟨407989430748042953145997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543985907664057270861329 407989430748042953145997)
            ·
              refine ⟨152996036530516107429749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407989430748042953145997 152996036530516107429749)
              ·
                refine ⟨14343378424735885071539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152996036530516107429749 14343378424735885071539)
                ·
                  rfl

theorem cell19_47138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_47138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47138 prefixEnd_47138 := by exact prefixLift 47138
  have htrace : WordTrace (prefixWord ++ tailWord_47138) baseStart_47138 baseEnd_47138 := by
    simpa [prefixWord, tailWord_47138, baseEnd_47138] using wordTrace_append hprefix tailTrace_47138
  have hstable : (prefixWord ++ tailWord_47138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47138).length < 2 ^ (prefixWord ++ tailWord_47138).sum := by decide
  have hdescent : baseEnd_47138 < baseStart_47138 := by decide
  rcases family_descends (prefixWord ++ tailWord_47138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47159 : List Nat := [1, 1, 3, 1, 2, 2, 9]
def baseStart_47159 : Nat := 118140960795 + 47159 * 2 ^ 59
def prefixEnd_47159 : Nat := 4983230072969 + 3 ^ 40 * 47159 * 2
def baseEnd_47159 : Nat := 4783256135404686201605

theorem tailTrace_47159 : CollatzResearch.WordTrace tailWord_47159 prefixEnd_47159 4783256135404686201605 := by
  unfold tailWord_47159
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720030036158471961088531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1146686690772314640725687 1720030036158471961088531)
  ·
    refine ⟨2580045054237707941632797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1720030036158471961088531 2580045054237707941632797)
    ·
      refine ⟨967516895339140478112299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2580045054237707941632797 967516895339140478112299)
      ·
        refine ⟨1451275343008710717168449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967516895339140478112299 1451275343008710717168449)
        ·
          refine ⟨1088456507256533037876337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1451275343008710717168449 1088456507256533037876337)
          ·
            refine ⟨816342380442399778407253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1088456507256533037876337 816342380442399778407253)
            ·
              refine ⟨4783256135404686201605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 816342380442399778407253 4783256135404686201605)
              ·
                rfl

theorem cell19_47159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_47159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47159 prefixEnd_47159 := by exact prefixLift 47159
  have htrace : WordTrace (prefixWord ++ tailWord_47159) baseStart_47159 baseEnd_47159 := by
    simpa [prefixWord, tailWord_47159, baseEnd_47159] using wordTrace_append hprefix tailTrace_47159
  have hstable : (prefixWord ++ tailWord_47159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47159).length < 2 ^ (prefixWord ++ tailWord_47159).sum := by decide
  have hdescent : baseEnd_47159 < baseStart_47159 := by decide
  rcases family_descends (prefixWord ++ tailWord_47159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47216 : List Nat := [2, 1, 1, 1, 5, 9]
def baseStart_47216 : Nat := 118140960795 + 47216 * 2 ^ 59
def prefixEnd_47216 : Nat := 4983230072969 + 3 ^ 40 * 47216 * 2
def baseEnd_47216 : Nat := 1596345849072757259777

theorem tailTrace_47216 : CollatzResearch.WordTrace tailWord_47216 prefixEnd_47216 1596345849072757259777 := by
  unfold tailWord_47216
  simp only [CollatzResearch.WordTrace]
  refine ⟨861054498475985347956751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1148072664634647130609001 861054498475985347956751)
  ·
    refine ⟨1291581747713978021935127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 861054498475985347956751 1291581747713978021935127)
    ·
      refine ⟨1937372621570967032902691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291581747713978021935127 1937372621570967032902691)
      ·
        refine ⟨2906058932356450549354037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937372621570967032902691 2906058932356450549354037)
        ·
          refine ⟨272443024908417239001941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2906058932356450549354037 272443024908417239001941)
          ·
            refine ⟨1596345849072757259777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 272443024908417239001941 1596345849072757259777)
            ·
              rfl

theorem cell19_47216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 9].length) (baseStart_47216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47216 prefixEnd_47216 := by exact prefixLift 47216
  have htrace : WordTrace (prefixWord ++ tailWord_47216) baseStart_47216 baseEnd_47216 := by
    simpa [prefixWord, tailWord_47216, baseEnd_47216] using wordTrace_append hprefix tailTrace_47216
  have hstable : (prefixWord ++ tailWord_47216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47216).length < 2 ^ (prefixWord ++ tailWord_47216).sum := by decide
  have hdescent : baseEnd_47216 < baseStart_47216 := by decide
  rcases family_descends (prefixWord ++ tailWord_47216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47250 : List Nat := [3, 2, 3, 1, 1, 1, 5, 3]
def baseStart_47250 : Nat := 118140960795 + 47250 * 2 ^ 59
def prefixEnd_47250 : Nat := 4983230072969 + 3 ^ 40 * 47250 * 2
def baseEnd_47250 : Nat := 14377458325952810582345

theorem tailTrace_47250 : CollatzResearch.WordTrace tailWord_47250 prefixEnd_47250 14377458325952810582345 := by
  unfold tailWord_47250
  simp only [CollatzResearch.WordTrace]
  refine ⟨430837269707198625662801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1148899385885863001767469 430837269707198625662801)
  ·
    refine ⟨323127952280398969247101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 430837269707198625662801 323127952280398969247101)
    ·
      refine ⟨121172982105149613467663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323127952280398969247101 121172982105149613467663)
      ·
        refine ⟨181759473157724420201495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121172982105149613467663 181759473157724420201495)
        ·
          refine ⟨272639209736586630302243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181759473157724420201495 272639209736586630302243)
          ·
            refine ⟨408958814604879945453365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272639209736586630302243 408958814604879945453365)
            ·
              refine ⟨38339888869207494886253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 408958814604879945453365 38339888869207494886253)
              ·
                refine ⟨14377458325952810582345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38339888869207494886253 14377458325952810582345)
                ·
                  rfl

theorem cell19_47250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_47250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47250 prefixEnd_47250 := by exact prefixLift 47250
  have htrace : WordTrace (prefixWord ++ tailWord_47250) baseStart_47250 baseEnd_47250 := by
    simpa [prefixWord, tailWord_47250, baseEnd_47250] using wordTrace_append hprefix tailTrace_47250
  have hstable : (prefixWord ++ tailWord_47250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47250).length < 2 ^ (prefixWord ++ tailWord_47250).sum := by decide
  have hdescent : baseEnd_47250 < baseStart_47250 := by decide
  rcases family_descends (prefixWord ++ tailWord_47250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47311 : List Nat := [1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_47311 : Nat := 118140960795 + 47311 * 2 ^ 59
def prefixEnd_47311 : Nat := 4983230072969 + 3 ^ 40 * 47311 * 2
def baseEnd_47311 : Nat := 14396019700722743226623

theorem tailTrace_47311 : CollatzResearch.WordTrace tailWord_47311 prefixEnd_47311 14396019700722743226623 := by
  unfold tailWord_47311
  simp only [CollatzResearch.WordTrace]
  refine ⟨1725573931607801920621787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1150382621071867947081191 1725573931607801920621787)
  ·
    refine ⟨2588360897411702880932681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1725573931607801920621787 2588360897411702880932681)
    ·
      refine ⟨1941270673058777160699511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2588360897411702880932681 1941270673058777160699511)
      ·
        refine ⟨2911906009588165741049267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1941270673058777160699511 2911906009588165741049267)
        ·
          refine ⟨4367859014382248611573901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911906009588165741049267 4367859014382248611573901)
          ·
            refine ⟨1637947130393343229340213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4367859014382248611573901 1637947130393343229340213)
            ·
              refine ⟨153557543474375927750645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1637947130393343229340213 153557543474375927750645)
              ·
                refine ⟨14396019700722743226623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153557543474375927750645 14396019700722743226623)
                ·
                  rfl

theorem cell19_47311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_47311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47311 prefixEnd_47311 := by exact prefixLift 47311
  have htrace : WordTrace (prefixWord ++ tailWord_47311) baseStart_47311 baseEnd_47311 := by
    simpa [prefixWord, tailWord_47311, baseEnd_47311] using wordTrace_append hprefix tailTrace_47311
  have hstable : (prefixWord ++ tailWord_47311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47311).length < 2 ^ (prefixWord ++ tailWord_47311).sum := by decide
  have hdescent : baseEnd_47311 < baseStart_47311 := by decide
  rcases family_descends (prefixWord ++ tailWord_47311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47324 : List Nat := [2, 2, 5, 2, 1, 2, 5]
def baseStart_47324 : Nat := 118140960795 + 47324 * 2 ^ 59
def prefixEnd_47324 : Nat := 4983230072969 + 3 ^ 40 * 47324 * 2
def baseEnd_47324 : Nat := 4799991801180854979233

theorem tailTrace_47324 : CollatzResearch.WordTrace tailWord_47324 prefixEnd_47324 4799991801180854979233 := by
  unfold tailWord_47324
  simp only [CollatzResearch.WordTrace]
  refine ⟨863024040280352570422513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1150698720373803427230017 863024040280352570422513)
  ·
    refine ⟨647268030210264427816885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 863024040280352570422513 647268030210264427816885)
    ·
      refine ⟨60681377832212290107833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 647268030210264427816885 60681377832212290107833)
      ·
        refine ⟨45511033374159217580875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60681377832212290107833 45511033374159217580875)
        ·
          refine ⟨68266550061238826371313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45511033374159217580875 68266550061238826371313)
          ·
            refine ⟨51199912545929119778485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68266550061238826371313 51199912545929119778485)
            ·
              refine ⟨4799991801180854979233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51199912545929119778485 4799991801180854979233)
              ·
                rfl

theorem cell19_47324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_47324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47324 prefixEnd_47324 := by exact prefixLift 47324
  have htrace : WordTrace (prefixWord ++ tailWord_47324) baseStart_47324 baseEnd_47324 := by
    simpa [prefixWord, tailWord_47324, baseEnd_47324] using wordTrace_append hprefix tailTrace_47324
  have hstable : (prefixWord ++ tailWord_47324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47324).length < 2 ^ (prefixWord ++ tailWord_47324).sum := by decide
  have hdescent : baseEnd_47324 < baseStart_47324 := by decide
  rcases family_descends (prefixWord ++ tailWord_47324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47400 : List Nat := [2, 1, 5, 1, 4, 1, 1, 4]
def baseStart_47400 : Nat := 118140960795 + 47400 * 2 ^ 59
def prefixEnd_47400 : Nat := 4983230072969 + 3 ^ 40 * 47400 * 2
def baseEnd_47400 : Nat := 14423101050796907248603

theorem tailTrace_47400 : CollatzResearch.WordTrace tailWord_47400 prefixEnd_47400 14423101050796907248603 := by
  unfold tailWord_47400
  simp only [CollatzResearch.WordTrace]
  refine ⟨864410014142685060305827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1152546685523580080407769 864410014142685060305827)
  ·
    refine ⟨1296615021214027590458741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 864410014142685060305827 1296615021214027590458741)
    ·
      refine ⟨121557658238815086605507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1296615021214027590458741 121557658238815086605507)
      ·
        refine ⟨182336487358222629908261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121557658238815086605507 182336487358222629908261)
        ·
          refine ⟨34188091379666743107799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182336487358222629908261 34188091379666743107799)
          ·
            refine ⟨51282137069500114661699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34188091379666743107799 51282137069500114661699)
            ·
              refine ⟨76923205604250171992549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51282137069500114661699 76923205604250171992549)
              ·
                refine ⟨14423101050796907248603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76923205604250171992549 14423101050796907248603)
                ·
                  rfl

theorem cell19_47400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_47400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47400 prefixEnd_47400 := by exact prefixLift 47400
  have htrace : WordTrace (prefixWord ++ tailWord_47400) baseStart_47400 baseEnd_47400 := by
    simpa [prefixWord, tailWord_47400, baseEnd_47400] using wordTrace_append hprefix tailTrace_47400
  have hstable : (prefixWord ++ tailWord_47400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47400).length < 2 ^ (prefixWord ++ tailWord_47400).sum := by decide
  have hdescent : baseEnd_47400 < baseStart_47400 := by decide
  rcases family_descends (prefixWord ++ tailWord_47400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47423 : List Nat := [1, 1, 2, 2, 4, 1, 5, 3]
def baseStart_47423 : Nat := 118140960795 + 47423 * 2 ^ 59
def prefixEnd_47423 : Nat := 4983230072969 + 3 ^ 40 * 47423 * 2
def baseEnd_47423 : Nat := 14430099601939668737429

theorem tailTrace_47423 : CollatzResearch.WordTrace tailWord_47423 prefixEnd_47423 14430099601939668737429 := by
  unfold tailWord_47423
  simp only [CollatzResearch.WordTrace]
  refine ⟨1729658907202045048698923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1153105938134696699132615 1729658907202045048698923)
  ·
    refine ⟨2594488360803067573048385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1729658907202045048698923 2594488360803067573048385)
    ·
      refine ⟨1945866270602300679786289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2594488360803067573048385 1945866270602300679786289)
      ·
        refine ⟨1459399702951725509839717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1945866270602300679786289 1459399702951725509839717)
        ·
          refine ⟨273637444303448533094947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1459399702951725509839717 273637444303448533094947)
          ·
            refine ⟨410456166455172799642421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273637444303448533094947 410456166455172799642421)
            ·
              refine ⟨38480265605172449966477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 410456166455172799642421 38480265605172449966477)
              ·
                refine ⟨14430099601939668737429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38480265605172449966477 14430099601939668737429)
                ·
                  rfl

theorem cell19_47423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 3].length) (baseStart_47423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47423 prefixEnd_47423 := by exact prefixLift 47423
  have htrace : WordTrace (prefixWord ++ tailWord_47423) baseStart_47423 baseEnd_47423 := by
    simpa [prefixWord, tailWord_47423, baseEnd_47423] using wordTrace_append hprefix tailTrace_47423
  have hstable : (prefixWord ++ tailWord_47423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47423).length < 2 ^ (prefixWord ++ tailWord_47423).sum := by decide
  have hdescent : baseEnd_47423 < baseStart_47423 := by decide
  rcases family_descends (prefixWord ++ tailWord_47423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47520 : List Nat := [2, 1, 1, 4, 1, 3, 1, 6]
def baseStart_47520 : Nat := 118140960795 + 47520 * 2 ^ 59
def prefixEnd_47520 : Nat := 4983230072969 + 3 ^ 40 * 47520 * 2
def baseEnd_47520 : Nat := 14459615230672184581609

theorem tailTrace_47520 : CollatzResearch.WordTrace tailWord_47520 prefixEnd_47520 14459615230672184581609 := by
  unfold tailWord_47520
  simp only [CollatzResearch.WordTrace]
  refine ⟨866598393925315307490007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1155464525233753743320009 866598393925315307490007)
  ·
    refine ⟨1299897590887972961235011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 866598393925315307490007 1299897590887972961235011)
    ·
      refine ⟨1949846386331959441852517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299897590887972961235011 1949846386331959441852517)
      ·
        refine ⟨365596197437242395347347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1949846386331959441852517 365596197437242395347347)
        ·
          refine ⟨548394296155863593021021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365596197437242395347347 548394296155863593021021)
          ·
            refine ⟨205647861058448847382883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 548394296155863593021021 205647861058448847382883)
            ·
              refine ⟨308471791587673271074325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205647861058448847382883 308471791587673271074325)
              ·
                refine ⟨14459615230672184581609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 308471791587673271074325 14459615230672184581609)
                ·
                  rfl

theorem cell19_47520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_47520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47520 prefixEnd_47520 := by exact prefixLift 47520
  have htrace : WordTrace (prefixWord ++ tailWord_47520) baseStart_47520 baseEnd_47520 := by
    simpa [prefixWord, tailWord_47520, baseEnd_47520] using wordTrace_append hprefix tailTrace_47520
  have hstable : (prefixWord ++ tailWord_47520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47520).length < 2 ^ (prefixWord ++ tailWord_47520).sum := by decide
  have hdescent : baseEnd_47520 < baseStart_47520 := by decide
  rcases family_descends (prefixWord ++ tailWord_47520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47554 : List Nat := [3, 5, 2, 9]
def baseStart_47554 : Nat := 118140960795 + 47554 * 2 ^ 59
def prefixEnd_47554 : Nat := 4983230072969 + 3 ^ 40 * 47554 * 2
def baseEnd_47554 : Nat := 178641492777409627481

theorem tailTrace_47554 : CollatzResearch.WordTrace tailWord_47554 prefixEnd_47554 178641492777409627481 := by
  unfold tailWord_47554
  simp only [CollatzResearch.WordTrace]
  refine ⟨433609217431863605429429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1156291246484969614478477 433609217431863605429429)
  ·
    refine ⟨40650864134237213009009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 433609217431863605429429 40650864134237213009009)
    ·
      refine ⟨30488148100677909756757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40650864134237213009009 30488148100677909756757)
      ·
        refine ⟨178641492777409627481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 30488148100677909756757 178641492777409627481)
        ·
          rfl

theorem cell19_47554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 9].length) (baseStart_47554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47554 prefixEnd_47554 := by exact prefixLift 47554
  have htrace : WordTrace (prefixWord ++ tailWord_47554) baseStart_47554 baseEnd_47554 := by
    simpa [prefixWord, tailWord_47554, baseEnd_47554] using wordTrace_append hprefix tailTrace_47554
  have hstable : (prefixWord ++ tailWord_47554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47554).length < 2 ^ (prefixWord ++ tailWord_47554).sum := by decide
  have hdescent : baseEnd_47554 < baseStart_47554 := by decide
  rcases family_descends (prefixWord ++ tailWord_47554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47556 : List Nat := [2, 3, 3, 2, 2, 7]
def baseStart_47556 : Nat := 118140960795 + 47556 * 2 ^ 59
def prefixEnd_47556 : Nat := 4983230072969 + 3 ^ 40 * 47556 * 2
def baseEnd_47556 : Nat := 1607841053848307531279

theorem tailTrace_47556 : CollatzResearch.WordTrace tailWord_47556 prefixEnd_47556 1607841053848307531279 := by
  unfold tailWord_47556
  simp only [CollatzResearch.WordTrace]
  refine ⟨867254907860104381645261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1156339877146805842193681 867254907860104381645261)
  ·
    refine ⟨325220590447539143116973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 867254907860104381645261 325220590447539143116973)
    ·
      refine ⟨121957721417827178668865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325220590447539143116973 121957721417827178668865)
      ·
        refine ⟨91468291063370384001649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121957721417827178668865 91468291063370384001649)
        ·
          refine ⟨68601218297527788001237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91468291063370384001649 68601218297527788001237)
          ·
            refine ⟨1607841053848307531279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 68601218297527788001237 1607841053848307531279)
            ·
              rfl

theorem cell19_47556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 7].length) (baseStart_47556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47556 prefixEnd_47556 := by exact prefixLift 47556
  have htrace : WordTrace (prefixWord ++ tailWord_47556) baseStart_47556 baseEnd_47556 := by
    simpa [prefixWord, tailWord_47556, baseEnd_47556] using wordTrace_append hprefix tailTrace_47556
  have hstable : (prefixWord ++ tailWord_47556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47556).length < 2 ^ (prefixWord ++ tailWord_47556).sum := by decide
  have hdescent : baseEnd_47556 < baseStart_47556 := by decide
  rcases family_descends (prefixWord ++ tailWord_47556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47651 : List Nat := [1, 1, 1, 4, 4, 1, 4, 3]
def baseStart_47651 : Nat := 118140960795 + 47651 * 2 ^ 59
def prefixEnd_47651 : Nat := 4983230072969 + 3 ^ 40 * 47651 * 2
def baseEnd_47651 : Nat := 14499476543702695670141

theorem tailTrace_47651 : CollatzResearch.WordTrace tailWord_47651 prefixEnd_47651 14499476543702695670141 := by
  unfold tailWord_47651
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737974750376039987998807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1158649833584026658665871 1737974750376039987998807)
  ·
    refine ⟨2606962125564059981998211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1737974750376039987998807 2606962125564059981998211)
    ·
      refine ⟨3910443188346089972997317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606962125564059981998211 3910443188346089972997317)
      ·
        refine ⟨733208097814891869936997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3910443188346089972997317 733208097814891869936997)
        ·
          refine ⟨137476518340292225613187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 733208097814891869936997 137476518340292225613187)
          ·
            refine ⟨206214777510438338419781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137476518340292225613187 206214777510438338419781)
            ·
              refine ⟨38665270783207188453709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206214777510438338419781 38665270783207188453709)
              ·
                refine ⟨14499476543702695670141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38665270783207188453709 14499476543702695670141)
                ·
                  rfl

theorem cell19_47651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_47651 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47651 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47651 prefixEnd_47651 := by exact prefixLift 47651
  have htrace : WordTrace (prefixWord ++ tailWord_47651) baseStart_47651 baseEnd_47651 := by
    simpa [prefixWord, tailWord_47651, baseEnd_47651] using wordTrace_append hprefix tailTrace_47651
  have hstable : (prefixWord ++ tailWord_47651).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47651).length < 2 ^ (prefixWord ++ tailWord_47651).sum := by decide
  have hdescent : baseEnd_47651 < baseStart_47651 := by decide
  rcases family_descends (prefixWord ++ tailWord_47651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47670 : List Nat := [5, 1, 2, 1, 2, 1, 7]
def baseStart_47670 : Nat := 118140960795 + 47670 * 2 ^ 59
def prefixEnd_47670 : Nat := 4983230072969 + 3 ^ 40 * 47670 * 2
def baseEnd_47670 : Nat := 4835085985172093749289

theorem tailTrace_47670 : CollatzResearch.WordTrace tailWord_47670 prefixEnd_47670 4835085985172093749289 := by
  unfold tailWord_47670
  simp only [CollatzResearch.WordTrace]
  refine ⟨108666733581700389558779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1159111824871470821960309 108666733581700389558779)
  ·
    refine ⟨163000100372550584338169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108666733581700389558779 163000100372550584338169)
    ·
      refine ⟨122250075279412938253627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163000100372550584338169 122250075279412938253627)
      ·
        refine ⟨183375112919119407380441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122250075279412938253627 183375112919119407380441)
        ·
          refine ⟨137531334689339555535331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183375112919119407380441 137531334689339555535331)
          ·
            refine ⟨206297002034009333302997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137531334689339555535331 206297002034009333302997)
            ·
              refine ⟨4835085985172093749289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 206297002034009333302997 4835085985172093749289)
              ·
                rfl

theorem cell19_47670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_47670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47670 prefixEnd_47670 := by exact prefixLift 47670
  have htrace : WordTrace (prefixWord ++ tailWord_47670) baseStart_47670 baseEnd_47670 := by
    simpa [prefixWord, tailWord_47670, baseEnd_47670] using wordTrace_append hprefix tailTrace_47670
  have hstable : (prefixWord ++ tailWord_47670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47670).length < 2 ^ (prefixWord ++ tailWord_47670).sum := by decide
  have hdescent : baseEnd_47670 < baseStart_47670 := by decide
  rcases family_descends (prefixWord ++ tailWord_47670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47814 : List Nat := [6, 1, 2, 1, 3, 1, 2, 3]
def baseStart_47814 : Nat := 118140960795 + 47814 * 2 ^ 59
def prefixEnd_47814 : Nat := 4983230072969 + 3 ^ 40 * 47814 * 2
def baseEnd_47814 : Nat := 14549074971366614047475

theorem tailTrace_47814 : CollatzResearch.WordTrace tailWord_47814 prefixEnd_47814 14549074971366614047475 := by
  unfold tailWord_47814
  simp only [CollatzResearch.WordTrace]
  refine ⟨54497495274547463318203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1162613232523679217454997 54497495274547463318203)
  ·
    refine ⟨81746242911821194977305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54497495274547463318203 81746242911821194977305)
    ·
      refine ⟨61309682183865896232979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81746242911821194977305 61309682183865896232979)
      ·
        refine ⟨91964523275798844349469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61309682183865896232979 91964523275798844349469)
        ·
          refine ⟨34486696228424566631051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91964523275798844349469 34486696228424566631051)
          ·
            refine ⟨51730044342636849946577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34486696228424566631051 51730044342636849946577)
            ·
              refine ⟨38797533256977637459933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51730044342636849946577 38797533256977637459933)
              ·
                refine ⟨14549074971366614047475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38797533256977637459933 14549074971366614047475)
                ·
                  rfl

theorem cell19_47814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_47814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47814 prefixEnd_47814 := by exact prefixLift 47814
  have htrace : WordTrace (prefixWord ++ tailWord_47814) baseStart_47814 baseEnd_47814 := by
    simpa [prefixWord, tailWord_47814, baseEnd_47814] using wordTrace_append hprefix tailTrace_47814
  have hstable : (prefixWord ++ tailWord_47814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47814).length < 2 ^ (prefixWord ++ tailWord_47814).sum := by decide
  have hdescent : baseEnd_47814 < baseStart_47814 := by decide
  rcases family_descends (prefixWord ++ tailWord_47814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47820 : List Nat := [2, 2, 1, 5, 1, 3, 2, 3]
def baseStart_47820 : Nat := 118140960795 + 47820 * 2 ^ 59
def prefixEnd_47820 : Nat := 4983230072969 + 3 ^ 40 * 47820 * 2
def baseEnd_47820 : Nat := 14550900680360377914125

theorem tailTrace_47820 : CollatzResearch.WordTrace tailWord_47820 prefixEnd_47820 14550900680360377914125 := by
  unfold tailWord_47820
  simp only [CollatzResearch.WordTrace]
  refine ⟨872069343381890925450457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1162759124509187900600609 872069343381890925450457)
  ·
    refine ⟨654052007536418194087843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 872069343381890925450457 654052007536418194087843)
    ·
      refine ⟨981078011304627291131765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 654052007536418194087843 981078011304627291131765)
      ·
        refine ⟨91976063559808808543603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 981078011304627291131765 91976063559808808543603)
        ·
          refine ⟨137964095339713212815405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91976063559808808543603 137964095339713212815405)
          ·
            refine ⟨51736535752392454805777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137964095339713212815405 51736535752392454805777)
            ·
              refine ⟨38802401814294341104333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51736535752392454805777 38802401814294341104333)
              ·
                refine ⟨14550900680360377914125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38802401814294341104333 14550900680360377914125)
                ·
                  rfl

theorem cell19_47820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_47820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47820 prefixEnd_47820 := by exact prefixLift 47820
  have htrace : WordTrace (prefixWord ++ tailWord_47820) baseStart_47820 baseEnd_47820 := by
    simpa [prefixWord, tailWord_47820, baseEnd_47820] using wordTrace_append hprefix tailTrace_47820
  have hstable : (prefixWord ++ tailWord_47820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47820).length < 2 ^ (prefixWord ++ tailWord_47820).sum := by decide
  have hdescent : baseEnd_47820 < baseStart_47820 := by decide
  rcases family_descends (prefixWord ++ tailWord_47820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47822 : List Nat := [4, 1, 1, 1, 3, 2, 4, 3]
def baseStart_47822 : Nat := 118140960795 + 47822 * 2 ^ 59
def prefixEnd_47822 : Nat := 4983230072969 + 3 ^ 40 * 47822 * 2
def baseEnd_47822 : Nat := 14551509250024965869675

theorem tailTrace_47822 : CollatzResearch.WordTrace tailWord_47822 prefixEnd_47822 14551509250024965869675 := by
  unfold tailWord_47822
  simp only [CollatzResearch.WordTrace]
  refine ⟨218026454094567024059215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1162807755171024128315813 218026454094567024059215)
  ·
    refine ⟨327039681141850536088823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218026454094567024059215 327039681141850536088823)
    ·
      refine ⟨490559521712775804133235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327039681141850536088823 490559521712775804133235)
      ·
        refine ⟨735839282569163706199853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490559521712775804133235 735839282569163706199853)
        ·
          refine ⟨275939730963436389824945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 735839282569163706199853 275939730963436389824945)
          ·
            refine ⟨206954798222577292368709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275939730963436389824945 206954798222577292368709)
            ·
              refine ⟨38804024666733242319133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206954798222577292368709 38804024666733242319133)
              ·
                refine ⟨14551509250024965869675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38804024666733242319133 14551509250024965869675)
                ·
                  rfl

theorem cell19_47822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_47822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47822 prefixEnd_47822 := by exact prefixLift 47822
  have htrace : WordTrace (prefixWord ++ tailWord_47822) baseStart_47822 baseEnd_47822 := by
    simpa [prefixWord, tailWord_47822, baseEnd_47822] using wordTrace_append hprefix tailTrace_47822
  have hstable : (prefixWord ++ tailWord_47822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47822).length < 2 ^ (prefixWord ++ tailWord_47822).sum := by decide
  have hdescent : baseEnd_47822 < baseStart_47822 := by decide
  rcases family_descends (prefixWord ++ tailWord_47822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47843 : List Nat := [1, 1, 1, 7, 1, 1, 7]
def baseStart_47843 : Nat := 118140960795 + 47843 * 2 ^ 59
def prefixEnd_47843 : Nat := 4983230072969 + 3 ^ 40 * 47843 * 2
def baseEnd_47843 : Nat := 4852633077167713134317

theorem tailTrace_47843 : CollatzResearch.WordTrace tailWord_47843 prefixEnd_47843 4852633077167713134317 := by
  unfold tailWord_47843
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744977565680456778988183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1163318377120304519325455 1744977565680456778988183)
  ·
    refine ⟨2617466348520685168482275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1744977565680456778988183 2617466348520685168482275)
    ·
      refine ⟨3926199522781027752723413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2617466348520685168482275 3926199522781027752723413)
      ·
        refine ⟨92020301315180337954455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3926199522781027752723413 92020301315180337954455)
        ·
          refine ⟨138030451972770506931683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92020301315180337954455 138030451972770506931683)
          ·
            refine ⟨207045677959155760397525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138030451972770506931683 207045677959155760397525)
            ·
              refine ⟨4852633077167713134317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 207045677959155760397525 4852633077167713134317)
              ·
                rfl

theorem cell19_47843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_47843 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47843 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47843 prefixEnd_47843 := by exact prefixLift 47843
  have htrace : WordTrace (prefixWord ++ tailWord_47843) baseStart_47843 baseEnd_47843 := by
    simpa [prefixWord, tailWord_47843, baseEnd_47843] using wordTrace_append hprefix tailTrace_47843
  have hstable : (prefixWord ++ tailWord_47843).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47843).length < 2 ^ (prefixWord ++ tailWord_47843).sum := by decide
  have hdescent : baseEnd_47843 < baseStart_47843 := by decide
  rcases family_descends (prefixWord ++ tailWord_47843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47934 : List Nat := [4, 2, 1, 2, 3, 1, 3, 3]
def baseStart_47934 : Nat := 118140960795 + 47934 * 2 ^ 59
def prefixEnd_47934 : Nat := 4983230072969 + 3 ^ 40 * 47934 * 2
def baseEnd_47934 : Nat := 14585589151241891380481

theorem tailTrace_47934 : CollatzResearch.WordTrace tailWord_47934 prefixEnd_47934 14585589151241891380481 := by
  unfold tailWord_47934
  simp only [CollatzResearch.WordTrace]
  refine ⟨218537076043847415068857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1165531072233852880367237 218537076043847415068857)
  ·
    refine ⟨163902807032885561301643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218537076043847415068857 163902807032885561301643)
    ·
      refine ⟨245854210549328341952465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163902807032885561301643 245854210549328341952465)
      ·
        refine ⟨184390657911996256464349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 245854210549328341952465 184390657911996256464349)
        ·
          refine ⟨69146496716998596174131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184390657911996256464349 69146496716998596174131)
          ·
            refine ⟨103719745075497894261197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69146496716998596174131 103719745075497894261197)
            ·
              refine ⟨38894904403311710347949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103719745075497894261197 38894904403311710347949)
              ·
                refine ⟨14585589151241891380481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38894904403311710347949 14585589151241891380481)
                ·
                  rfl

theorem cell19_47934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_47934 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47934 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47934 prefixEnd_47934 := by exact prefixLift 47934
  have htrace : WordTrace (prefixWord ++ tailWord_47934) baseStart_47934 baseEnd_47934 := by
    simpa [prefixWord, tailWord_47934, baseEnd_47934] using wordTrace_append hprefix tailTrace_47934
  have hstable : (prefixWord ++ tailWord_47934).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47934).length < 2 ^ (prefixWord ++ tailWord_47934).sum := by decide
  have hdescent : baseEnd_47934 < baseStart_47934 := by decide
  rcases family_descends (prefixWord ++ tailWord_47934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47993 : List Nat := [1, 2, 1, 3, 2, 5, 2, 3]
def baseStart_47993 : Nat := 118140960795 + 47993 * 2 ^ 59
def prefixEnd_47993 : Nat := 4983230072969 + 3 ^ 40 * 47993 * 2
def baseEnd_47993 : Nat := 14603541956347236069209

theorem tailTrace_47993 : CollatzResearch.WordTrace tailWord_47993 prefixEnd_47993 14603541956347236069209 := by
  unfold tailWord_47993
  simp only [CollatzResearch.WordTrace]
  refine ⟨1750448515137032396948633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1166965676758021597965755 1750448515137032396948633)
  ·
    refine ⟨1312836386352774297711475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1750448515137032396948633 1312836386352774297711475)
    ·
      refine ⟨1969254579529161446567213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312836386352774297711475 1969254579529161446567213)
      ·
        refine ⟨738470467323435542462705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1969254579529161446567213 738470467323435542462705)
        ·
          refine ⟨553852850492576656847029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738470467323435542462705 553852850492576656847029)
          ·
            refine ⟨51923704733679061579409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 553852850492576656847029 51923704733679061579409)
            ·
              refine ⟨38942778550259296184557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51923704733679061579409 38942778550259296184557)
              ·
                refine ⟨14603541956347236069209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38942778550259296184557 14603541956347236069209)
                ·
                  rfl

theorem cell19_47993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_47993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47993 prefixEnd_47993 := by exact prefixLift 47993
  have htrace : WordTrace (prefixWord ++ tailWord_47993) baseStart_47993 baseEnd_47993 := by
    simpa [prefixWord, tailWord_47993, baseEnd_47993] using wordTrace_append hprefix tailTrace_47993
  have hstable : (prefixWord ++ tailWord_47993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47993).length < 2 ^ (prefixWord ++ tailWord_47993).sum := by decide
  have hdescent : baseEnd_47993 < baseStart_47993 := by decide
  rcases family_descends (prefixWord ++ tailWord_47993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47995 : List Nat := [1, 1, 1, 1, 1, 5, 6, 3]
def baseStart_47995 : Nat := 118140960795 + 47995 * 2 ^ 59
def prefixEnd_47995 : Nat := 4983230072969 + 3 ^ 40 * 47995 * 2
def baseEnd_47995 : Nat := 14604150526011824024759

theorem tailTrace_47995 : CollatzResearch.WordTrace tailWord_47995 prefixEnd_47995 14604150526011824024759 := by
  unfold tailWord_47995
  simp only [CollatzResearch.WordTrace]
  refine ⟨1750521461129786738521439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1167014307419857825680959 1750521461129786738521439)
  ·
    refine ⟨2625782191694680107782159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1750521461129786738521439 2625782191694680107782159)
    ·
      refine ⟨3938673287542020161673239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2625782191694680107782159 3938673287542020161673239)
      ·
        refine ⟨5908009931313030242509859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3938673287542020161673239 5908009931313030242509859)
        ·
          refine ⟨8862014896969545363764789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5908009931313030242509859 8862014896969545363764789)
          ·
            refine ⟨830813896590894877852949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8862014896969545363764789 830813896590894877852949)
            ·
              refine ⟨38944401402698197399357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 830813896590894877852949 38944401402698197399357)
              ·
                refine ⟨14604150526011824024759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38944401402698197399357 14604150526011824024759)
                ·
                  rfl

theorem cell19_47995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_47995 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_47995 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_47995 prefixEnd_47995 := by exact prefixLift 47995
  have htrace : WordTrace (prefixWord ++ tailWord_47995) baseStart_47995 baseEnd_47995 := by
    simpa [prefixWord, tailWord_47995, baseEnd_47995] using wordTrace_append hprefix tailTrace_47995
  have hstable : (prefixWord ++ tailWord_47995).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47995).length < 2 ^ (prefixWord ++ tailWord_47995).sum := by decide
  have hdescent : baseEnd_47995 < baseStart_47995 := by decide
  rcases family_descends (prefixWord ++ tailWord_47995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48033 : List Nat := [1, 2, 3, 4, 1, 1, 1, 6]
def baseStart_48033 : Nat := 118140960795 + 48033 * 2 ^ 59
def prefixEnd_48033 : Nat := 4983230072969 + 3 ^ 40 * 48033 * 2
def baseEnd_48033 : Nat := 14615713349638995180211

theorem tailTrace_48033 : CollatzResearch.WordTrace tailWord_48033 prefixEnd_48033 14615713349638995180211 := by
  unfold tailWord_48033
  simp only [CollatzResearch.WordTrace]
  refine ⟨1751907434992119228404753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1167938289994746152269835 1751907434992119228404753)
  ·
    refine ⟨1313930576244089421303565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1751907434992119228404753 1313930576244089421303565)
    ·
      refine ⟨492723966091533532988837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1313930576244089421303565 492723966091533532988837)
      ·
        refine ⟨92385743642162537435407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 492723966091533532988837 92385743642162537435407)
        ·
          refine ⟨138578615463243806153111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92385743642162537435407 138578615463243806153111)
          ·
            refine ⟨207867923194865709229667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138578615463243806153111 207867923194865709229667)
            ·
              refine ⟨311801884792298563844501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207867923194865709229667 311801884792298563844501)
              ·
                refine ⟨14615713349638995180211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 311801884792298563844501 14615713349638995180211)
                ·
                  rfl

theorem cell19_48033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_48033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48033 prefixEnd_48033 := by exact prefixLift 48033
  have htrace : WordTrace (prefixWord ++ tailWord_48033) baseStart_48033 baseEnd_48033 := by
    simpa [prefixWord, tailWord_48033, baseEnd_48033] using wordTrace_append hprefix tailTrace_48033
  have hstable : (prefixWord ++ tailWord_48033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48033).length < 2 ^ (prefixWord ++ tailWord_48033).sum := by decide
  have hdescent : baseEnd_48033 < baseStart_48033 := by decide
  rcases family_descends (prefixWord ++ tailWord_48033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48035 : List Nat := [1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_48035 : Nat := 118140960795 + 48035 * 2 ^ 59
def prefixEnd_48035 : Nat := 4983230072969 + 3 ^ 40 * 48035 * 2
def baseEnd_48035 : Nat := 14616321919303583135761

theorem tailTrace_48035 : CollatzResearch.WordTrace tailWord_48035 prefixEnd_48035 14616321919303583135761 := by
  unfold tailWord_48035
  simp only [CollatzResearch.WordTrace]
  refine ⟨1751980380984873569977559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1167986920656582379985039 1751980380984873569977559)
  ·
    refine ⟨2627970571477310354966339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1751980380984873569977559 2627970571477310354966339)
    ·
      refine ⟨3941955857215965532449509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2627970571477310354966339 3941955857215965532449509)
      ·
        refine ⟨739116723227993537334283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3941955857215965532449509 739116723227993537334283)
        ·
          refine ⟨1108675084841990306001425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739116723227993537334283 1108675084841990306001425)
          ·
            refine ⟨831506313631492729501069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108675084841990306001425 831506313631492729501069)
            ·
              refine ⟨311814867611809773562901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 831506313631492729501069 311814867611809773562901)
              ·
                refine ⟨14616321919303583135761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 311814867611809773562901 14616321919303583135761)
                ·
                  rfl

theorem cell19_48035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_48035 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48035 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48035 prefixEnd_48035 := by exact prefixLift 48035
  have htrace : WordTrace (prefixWord ++ tailWord_48035) baseStart_48035 baseEnd_48035 := by
    simpa [prefixWord, tailWord_48035, baseEnd_48035] using wordTrace_append hprefix tailTrace_48035
  have hstable : (prefixWord ++ tailWord_48035).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48035).length < 2 ^ (prefixWord ++ tailWord_48035).sum := by decide
  have hdescent : baseEnd_48035 < baseStart_48035 := by decide
  rcases family_descends (prefixWord ++ tailWord_48035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48086 : List Nat := [5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_48086 : Nat := 118140960795 + 48086 * 2 ^ 59
def prefixEnd_48086 : Nat := 4983230072969 + 3 ^ 40 * 48086 * 2
def baseEnd_48086 : Nat := 14631840445750576002289

theorem tailTrace_48086 : CollatzResearch.WordTrace tailWord_48086 prefixEnd_48086 14631840445750576002289 := by
  unfold tailWord_48086
  simp only [CollatzResearch.WordTrace]
  refine ⟨109615031487506830005257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1169227002533406186722741 109615031487506830005257)
  ·
    refine ⟨82211273615630122503943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109615031487506830005257 82211273615630122503943)
    ·
      refine ⟨123316910423445183755915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82211273615630122503943 123316910423445183755915)
      ·
        refine ⟨184975365635167775633873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123316910423445183755915 184975365635167775633873)
        ·
          refine ⟨138731524226375831725405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184975365635167775633873 138731524226375831725405)
          ·
            refine ⟨52024321584890936897027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138731524226375831725405 52024321584890936897027)
            ·
              refine ⟨78036482377336405345541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52024321584890936897027 78036482377336405345541)
              ·
                refine ⟨14631840445750576002289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78036482377336405345541 14631840445750576002289)
                ·
                  rfl

theorem cell19_48086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_48086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48086 prefixEnd_48086 := by exact prefixLift 48086
  have htrace : WordTrace (prefixWord ++ tailWord_48086) baseStart_48086 baseEnd_48086 := by
    simpa [prefixWord, tailWord_48086, baseEnd_48086] using wordTrace_append hprefix tailTrace_48086
  have hstable : (prefixWord ++ tailWord_48086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48086).length < 2 ^ (prefixWord ++ tailWord_48086).sum := by decide
  have hdescent : baseEnd_48086 < baseStart_48086 := by decide
  rcases family_descends (prefixWord ++ tailWord_48086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48090 : List Nat := [3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_48090 : Nat := 118140960795 + 48090 * 2 ^ 59
def prefixEnd_48090 : Nat := 4983230072969 + 3 ^ 40 * 48090 * 2
def baseEnd_48090 : Nat := 14633057585079751913389

theorem tailTrace_48090 : CollatzResearch.WordTrace tailWord_48090 prefixEnd_48090 14633057585079751913389 := by
  unfold tailWord_48090
  simp only [CollatzResearch.WordTrace]
  refine ⟨438496598946404490807431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1169324263857078642153149 438496598946404490807431)
  ·
    refine ⟨657744898419606736211147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 438496598946404490807431 657744898419606736211147)
    ·
      refine ⟨986617347629410104316721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 657744898419606736211147 986617347629410104316721)
      ·
        refine ⟨739963010722057578237541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 986617347629410104316721 739963010722057578237541)
        ·
          refine ⟨138743064510385795919539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 739963010722057578237541 138743064510385795919539)
          ·
            refine ⟨208114596765578693879309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138743064510385795919539 208114596765578693879309)
            ·
              refine ⟨78042973787092010204741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208114596765578693879309 78042973787092010204741)
              ·
                refine ⟨14633057585079751913389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78042973787092010204741 14633057585079751913389)
                ·
                  rfl

theorem cell19_48090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_48090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48090 prefixEnd_48090 := by exact prefixLift 48090
  have htrace : WordTrace (prefixWord ++ tailWord_48090) baseStart_48090 baseEnd_48090 := by
    simpa [prefixWord, tailWord_48090, baseEnd_48090] using wordTrace_append hprefix tailTrace_48090
  have hstable : (prefixWord ++ tailWord_48090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48090).length < 2 ^ (prefixWord ++ tailWord_48090).sum := by decide
  have hdescent : baseEnd_48090 < baseStart_48090 := by decide
  rcases family_descends (prefixWord ++ tailWord_48090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48126 : List Nat := [4, 2, 2, 2, 2, 1, 6]
def baseStart_48126 : Nat := 118140960795 + 48126 * 2 ^ 59
def prefixEnd_48126 : Nat := 4983230072969 + 3 ^ 40 * 48126 * 2
def baseEnd_48126 : Nat := 4881337279680778371097

theorem tailTrace_48126 : CollatzResearch.WordTrace tailWord_48126 prefixEnd_48126 4881337279680778371097 := by
  unfold tailWord_48126
  simp only [CollatzResearch.WordTrace]
  refine ⟨219412427956899513942529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1170199615770130741026821 219412427956899513942529)
  ·
    refine ⟨164559320967674635456897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219412427956899513942529 164559320967674635456897)
    ·
      refine ⟨123419490725755976592673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164559320967674635456897 123419490725755976592673)
      ·
        refine ⟨92564618044316982444505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123419490725755976592673 92564618044316982444505)
        ·
          refine ⟨69423463533237736833379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92564618044316982444505 69423463533237736833379)
          ·
            refine ⟨104135195299856605250069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69423463533237736833379 104135195299856605250069)
            ·
              refine ⟨4881337279680778371097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104135195299856605250069 4881337279680778371097)
              ·
                rfl

theorem cell19_48126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_48126 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48126 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48126 prefixEnd_48126 := by exact prefixLift 48126
  have htrace : WordTrace (prefixWord ++ tailWord_48126) baseStart_48126 baseEnd_48126 := by
    simpa [prefixWord, tailWord_48126, baseEnd_48126] using wordTrace_append hprefix tailTrace_48126
  have hstable : (prefixWord ++ tailWord_48126).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48126).length < 2 ^ (prefixWord ++ tailWord_48126).sum := by decide
  have hdescent : baseEnd_48126 < baseStart_48126 := by decide
  rcases family_descends (prefixWord ++ tailWord_48126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48160 : List Nat := [2, 1, 1, 7, 2, 1, 2, 3]
def baseStart_48160 : Nat := 118140960795 + 48160 * 2 ^ 59
def prefixEnd_48160 : Nat := 4983230072969 + 3 ^ 40 * 48160 * 2
def baseEnd_48160 : Nat := 14654357523340330357643

theorem tailTrace_48160 : CollatzResearch.WordTrace tailWord_48160 prefixEnd_48160 14654357523340330357643 := by
  unfold tailWord_48160
  simp only [CollatzResearch.WordTrace]
  refine ⟨878269752766009959138967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1171026337021346612185289 878269752766009959138967)
  ·
    refine ⟨1317404629149014938708451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 878269752766009959138967 1317404629149014938708451)
    ·
      refine ⟨1976106943723522408062677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317404629149014938708451 1976106943723522408062677)
      ·
        refine ⟨46315006493520056438969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 1976106943723522408062677 46315006493520056438969)
        ·
          refine ⟨34736254870140042329227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46315006493520056438969 34736254870140042329227)
          ·
            refine ⟨52104382305210063493841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34736254870140042329227 52104382305210063493841)
            ·
              refine ⟨39078286728907547620381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52104382305210063493841 39078286728907547620381)
              ·
                refine ⟨14654357523340330357643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39078286728907547620381 14654357523340330357643)
                ·
                  rfl

theorem cell19_48160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_48160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48160 prefixEnd_48160 := by exact prefixLift 48160
  have htrace : WordTrace (prefixWord ++ tailWord_48160) baseStart_48160 baseEnd_48160 := by
    simpa [prefixWord, tailWord_48160, baseEnd_48160] using wordTrace_append hprefix tailTrace_48160
  have hstable : (prefixWord ++ tailWord_48160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48160).length < 2 ^ (prefixWord ++ tailWord_48160).sum := by decide
  have hdescent : baseEnd_48160 < baseStart_48160 := by decide
  rcases family_descends (prefixWord ++ tailWord_48160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48164 : List Nat := [2, 3, 1, 4, 1, 1, 4, 3]
def baseStart_48164 : Nat := 118140960795 + 48164 * 2 ^ 59
def prefixEnd_48164 : Nat := 4983230072969 + 3 ^ 40 * 48164 * 2
def baseEnd_48164 : Nat := 14655574662669506268743

theorem tailTrace_48164 : CollatzResearch.WordTrace tailWord_48164 prefixEnd_48164 14655574662669506268743 := by
  unfold tailWord_48164
  simp only [CollatzResearch.WordTrace]
  refine ⟨878342698758764300711773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1171123598345019067615697 878342698758764300711773)
  ·
    refine ⟨329378512034536612766915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 878342698758764300711773 329378512034536612766915)
    ·
      refine ⟨494067768051804919150373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329378512034536612766915 494067768051804919150373)
      ·
        refine ⟨92637706509713422340695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 494067768051804919150373 92637706509713422340695)
        ·
          refine ⟨138956559764570133511043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92637706509713422340695 138956559764570133511043)
          ·
            refine ⟨208434839646855200266565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138956559764570133511043 208434839646855200266565)
            ·
              refine ⟨39081532433785350049981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208434839646855200266565 39081532433785350049981)
              ·
                refine ⟨14655574662669506268743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39081532433785350049981 14655574662669506268743)
                ·
                  rfl

theorem cell19_48164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_48164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48164 prefixEnd_48164 := by exact prefixLift 48164
  have htrace : WordTrace (prefixWord ++ tailWord_48164) baseStart_48164 baseEnd_48164 := by
    simpa [prefixWord, tailWord_48164, baseEnd_48164] using wordTrace_append hprefix tailTrace_48164
  have hstable : (prefixWord ++ tailWord_48164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48164).length < 2 ^ (prefixWord ++ tailWord_48164).sum := by decide
  have hdescent : baseEnd_48164 < baseStart_48164 := by decide
  rcases family_descends (prefixWord ++ tailWord_48164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48185 : List Nat := [1, 2, 1, 5, 2, 3, 5]
def baseStart_48185 : Nat := 118140960795 + 48185 * 2 ^ 59
def prefixEnd_48185 : Nat := 4983230072969 + 3 ^ 40 * 48185 * 2
def baseEnd_48185 : Nat := 4887321548049226600673

theorem tailTrace_48185 : CollatzResearch.WordTrace tailWord_48185 prefixEnd_48185 4887321548049226600673 := by
  unfold tailWord_48185
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757451330441449187938009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1171634220294299458625339 1757451330441449187938009)
  ·
    refine ⟨1318088497831086890953507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1757451330441449187938009 1318088497831086890953507)
    ·
      refine ⟨1977132746746630336430261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1318088497831086890953507 1977132746746630336430261)
      ·
        refine ⟨185356195007496594040337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1977132746746630336430261 185356195007496594040337)
        ·
          refine ⟨139017146255622445530253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185356195007496594040337 139017146255622445530253)
          ·
            refine ⟨52131429845858417073845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139017146255622445530253 52131429845858417073845)
            ·
              refine ⟨4887321548049226600673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52131429845858417073845 4887321548049226600673)
              ·
                rfl

theorem cell19_48185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_48185 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48185 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48185 prefixEnd_48185 := by exact prefixLift 48185
  have htrace : WordTrace (prefixWord ++ tailWord_48185) baseStart_48185 baseEnd_48185 := by
    simpa [prefixWord, tailWord_48185, baseEnd_48185] using wordTrace_append hprefix tailTrace_48185
  have hstable : (prefixWord ++ tailWord_48185).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48185).length < 2 ^ (prefixWord ++ tailWord_48185).sum := by decide
  have hdescent : baseEnd_48185 < baseStart_48185 := by decide
  rcases family_descends (prefixWord ++ tailWord_48185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48225 : List Nat := [1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_48225 : Nat := 118140960795 + 48225 * 2 ^ 59
def prefixEnd_48225 : Nat := 4983230072969 + 3 ^ 40 * 48225 * 2
def baseEnd_48225 : Nat := 14674136037439438913021

theorem tailTrace_48225 : CollatzResearch.WordTrace tailWord_48225 prefixEnd_48225 14674136037439438913021 := by
  unfold tailWord_48225
  simp only [CollatzResearch.WordTrace]
  refine ⟨1758910250296536019394129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1172606833531024012929419 1758910250296536019394129)
  ·
    refine ⟨1319182687722402014545597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1758910250296536019394129 1319182687722402014545597)
    ·
      refine ⟨494693507895900755454599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1319182687722402014545597 494693507895900755454599)
      ·
        refine ⟨742040261843851133181899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494693507895900755454599 742040261843851133181899)
        ·
          refine ⟨1113060392765776699772849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742040261843851133181899 1113060392765776699772849)
          ·
            refine ⟨834795294574332524829637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113060392765776699772849 834795294574332524829637)
            ·
              refine ⟨156524117732687348405557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 834795294574332524829637 156524117732687348405557)
              ·
                refine ⟨14674136037439438913021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156524117732687348405557 14674136037439438913021)
                ·
                  rfl

theorem cell19_48225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_48225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48225 prefixEnd_48225 := by exact prefixLift 48225
  have htrace : WordTrace (prefixWord ++ tailWord_48225) baseStart_48225 baseEnd_48225 := by
    simpa [prefixWord, tailWord_48225, baseEnd_48225] using wordTrace_append hprefix tailTrace_48225
  have hstable : (prefixWord ++ tailWord_48225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48225).length < 2 ^ (prefixWord ++ tailWord_48225).sum := by decide
  have hdescent : baseEnd_48225 < baseStart_48225 := by decide
  rcases family_descends (prefixWord ++ tailWord_48225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48333 : List Nat := [1, 6, 2, 2, 1, 1, 1, 5]
def baseStart_48333 : Nat := 118140960795 + 48333 * 2 ^ 59
def prefixEnd_48333 : Nat := 4983230072969 + 3 ^ 40 * 48333 * 2
def baseEnd_48333 : Nat := 14706998799327188512727

theorem tailTrace_48333 : CollatzResearch.WordTrace tailWord_48333 prefixEnd_48333 14706998799327188512727 := by
  unfold tailWord_48333
  simp only [CollatzResearch.WordTrace]
  refine ⟨1762849333905270464325653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1175232889270180309550435 1762849333905270464325653)
  ·
    refine ⟨82633562526809553015265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1762849333905270464325653 82633562526809553015265)
    ·
      refine ⟨61975171895107164761449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82633562526809553015265 61975171895107164761449)
      ·
        refine ⟨46481378921330373571087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61975171895107164761449 46481378921330373571087)
        ·
          refine ⟨69722068381995560356631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46481378921330373571087 69722068381995560356631)
          ·
            refine ⟨104583102572993340534947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69722068381995560356631 104583102572993340534947)
            ·
              refine ⟨156874653859490010802421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104583102572993340534947 156874653859490010802421)
              ·
                refine ⟨14706998799327188512727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156874653859490010802421 14706998799327188512727)
                ·
                  rfl

theorem cell19_48333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_48333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48333 prefixEnd_48333 := by exact prefixLift 48333
  have htrace : WordTrace (prefixWord ++ tailWord_48333) baseStart_48333 baseEnd_48333 := by
    simpa [prefixWord, tailWord_48333, baseEnd_48333] using wordTrace_append hprefix tailTrace_48333
  have hstable : (prefixWord ++ tailWord_48333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48333).length < 2 ^ (prefixWord ++ tailWord_48333).sum := by decide
  have hdescent : baseEnd_48333 < baseStart_48333 := by decide
  rcases family_descends (prefixWord ++ tailWord_48333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48377 : List Nat := [1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_48377 : Nat := 118140960795 + 48377 * 2 ^ 59
def prefixEnd_48377 : Nat := 4983230072969 + 3 ^ 40 * 48377 * 2
def baseEnd_48377 : Nat := 14720387331948123534829

theorem tailTrace_48377 : CollatzResearch.WordTrace tailWord_48377 prefixEnd_48377 14720387331948123534829 := by
  unfold tailWord_48377
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764454145745865978927385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1176302763830577319284923 1764454145745865978927385)
  ·
    refine ⟨1323340609309399484195539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1764454145745865978927385 1323340609309399484195539)
    ·
      refine ⟨1985010913964099226293309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323340609309399484195539 1985010913964099226293309)
      ·
        refine ⟨744379092736537209859991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1985010913964099226293309 744379092736537209859991)
        ·
          refine ⟨1116568639104805814789987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744379092736537209859991 1116568639104805814789987)
          ·
            refine ⟨1674852958657208722184981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116568639104805814789987 1674852958657208722184981)
            ·
              refine ⟨78508732437056658852421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1674852958657208722184981 78508732437056658852421)
              ·
                refine ⟨14720387331948123534829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78508732437056658852421 14720387331948123534829)
                ·
                  rfl

theorem cell19_48377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_48377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48377 prefixEnd_48377 := by exact prefixLift 48377
  have htrace : WordTrace (prefixWord ++ tailWord_48377) baseStart_48377 baseEnd_48377 := by
    simpa [prefixWord, tailWord_48377, baseEnd_48377] using wordTrace_append hprefix tailTrace_48377
  have hstable : (prefixWord ++ tailWord_48377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48377).length < 2 ^ (prefixWord ++ tailWord_48377).sum := by decide
  have hdescent : baseEnd_48377 < baseStart_48377 := by decide
  rcases family_descends (prefixWord ++ tailWord_48377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48396 : List Nat := [2, 2, 1, 2, 2, 3, 2, 5]
def baseStart_48396 : Nat := 118140960795 + 48396 * 2 ^ 59
def prefixEnd_48396 : Nat := 4983230072969 + 3 ^ 40 * 48396 * 2
def baseEnd_48396 : Nat := 14726168743761709112555

theorem tailTrace_48396 : CollatzResearch.WordTrace tailWord_48396 prefixEnd_48396 14726168743761709112555 := by
  unfold tailWord_48396
  simp only [CollatzResearch.WordTrace]
  refine ⟨882573566338516111934521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1176764755118021482579361 882573566338516111934521)
  ·
    refine ⟨661930174753887083950891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 882573566338516111934521 661930174753887083950891)
    ·
      refine ⟨992895262130830625926337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661930174753887083950891 992895262130830625926337)
      ·
        refine ⟨744671446598122969444753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 992895262130830625926337 744671446598122969444753)
        ·
          refine ⟨558503584948592227083565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744671446598122969444753 558503584948592227083565)
          ·
            refine ⟨209438844355722085156337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 558503584948592227083565 209438844355722085156337)
            ·
              refine ⟨157079133266791563867253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209438844355722085156337 157079133266791563867253)
              ·
                refine ⟨14726168743761709112555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 157079133266791563867253 14726168743761709112555)
                ·
                  rfl

theorem cell19_48396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_48396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48396 prefixEnd_48396 := by exact prefixLift 48396
  have htrace : WordTrace (prefixWord ++ tailWord_48396) baseStart_48396 baseEnd_48396 := by
    simpa [prefixWord, tailWord_48396, baseEnd_48396] using wordTrace_append hprefix tailTrace_48396
  have hstable : (prefixWord ++ tailWord_48396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48396).length < 2 ^ (prefixWord ++ tailWord_48396).sum := by decide
  have hdescent : baseEnd_48396 < baseStart_48396 := by decide
  rcases family_descends (prefixWord ++ tailWord_48396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48415 : List Nat := [1, 1, 2, 4, 4, 7]
def baseStart_48415 : Nat := 118140960795 + 48415 * 2 ^ 59
def prefixEnd_48415 : Nat := 4983230072969 + 3 ^ 40 * 48415 * 2
def baseEnd_48415 : Nat := 1636883350619477187809

theorem tailTrace_48415 : CollatzResearch.WordTrace tailWord_48415 prefixEnd_48415 1636883350619477187809 := by
  unfold tailWord_48415
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765840119608198468810699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1177226746405465645873799 1765840119608198468810699)
  ·
    refine ⟨2648760179412297703216049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1765840119608198468810699 2648760179412297703216049)
    ·
      refine ⟨1986570134559223277412037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2648760179412297703216049 1986570134559223277412037)
      ·
        refine ⟨372481900229854364514757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1986570134559223277412037 372481900229854364514757)
        ·
          refine ⟨69840356293097693346517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 372481900229854364514757 69840356293097693346517)
          ·
            refine ⟨1636883350619477187809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 69840356293097693346517 1636883350619477187809)
            ·
              rfl

theorem cell19_48415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 7].length) (baseStart_48415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48415 prefixEnd_48415 := by exact prefixLift 48415
  have htrace : WordTrace (prefixWord ++ tailWord_48415) baseStart_48415 baseEnd_48415 := by
    simpa [prefixWord, tailWord_48415, baseEnd_48415] using wordTrace_append hprefix tailTrace_48415
  have hstable : (prefixWord ++ tailWord_48415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48415).length < 2 ^ (prefixWord ++ tailWord_48415).sum := by decide
  have hdescent : baseEnd_48415 < baseStart_48415 := by decide
  rcases family_descends (prefixWord ++ tailWord_48415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48449 : List Nat := [1, 2, 5, 2, 1, 2, 3, 3]
def baseStart_48449 : Nat := 118140960795 + 48449 * 2 ^ 59
def prefixEnd_48449 : Nat := 4983230072969 + 3 ^ 40 * 48449 * 2
def baseEnd_48449 : Nat := 14742295839873289934633

theorem tailTrace_48449 : CollatzResearch.WordTrace tailWord_48449 prefixEnd_48449 14742295839873289934633 := by
  unfold tailWord_48449
  simp only [CollatzResearch.WordTrace]
  refine ⟨1767080201485022275548401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1178053467656681517032267 1767080201485022275548401)
  ·
    refine ⟨1325310151113766706661301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1767080201485022275548401 1325310151113766706661301)
    ·
      refine ⟨124247826666915628749497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1325310151113766706661301 124247826666915628749497)
      ·
        refine ⟨93185870000186721562123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124247826666915628749497 93185870000186721562123)
        ·
          refine ⟨139778805000280082343185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93185870000186721562123 139778805000280082343185)
          ·
            refine ⟨104834103750210061757389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139778805000280082343185 104834103750210061757389)
            ·
              refine ⟨39312788906328773159021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104834103750210061757389 39312788906328773159021)
              ·
                refine ⟨14742295839873289934633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39312788906328773159021 14742295839873289934633)
                ·
                  rfl

theorem cell19_48449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_48449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48449 prefixEnd_48449 := by exact prefixLift 48449
  have htrace : WordTrace (prefixWord ++ tailWord_48449) baseStart_48449 baseEnd_48449 := by
    simpa [prefixWord, tailWord_48449, baseEnd_48449] using wordTrace_append hprefix tailTrace_48449
  have hstable : (prefixWord ++ tailWord_48449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48449).length < 2 ^ (prefixWord ++ tailWord_48449).sum := by decide
  have hdescent : baseEnd_48449 < baseStart_48449 := by decide
  rcases family_descends (prefixWord ++ tailWord_48449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48546 : List Nat := [3, 3, 1, 2, 1, 3, 2, 4]
def baseStart_48546 : Nat := 118140960795 + 48546 * 2 ^ 59
def prefixEnd_48546 : Nat := 4983230072969 + 3 ^ 40 * 48546 * 2
def baseEnd_48546 : Nat := 14771811468605805778813

theorem tailTrace_48546 : CollatzResearch.WordTrace tailWord_48546 prefixEnd_48546 14771811468605805778813 := by
  unfold tailWord_48546
  simp only [CollatzResearch.WordTrace]
  refine ⟨442654520533401960457373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1180412054755738561219661 442654520533401960457373)
  ·
    refine ⟨165995445200025735171515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 442654520533401960457373 165995445200025735171515)
    ·
      refine ⟨248993167800038602757273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165995445200025735171515 248993167800038602757273)
      ·
        refine ⟨186744875850028952067955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 248993167800038602757273 186744875850028952067955)
        ·
          refine ⟨280117313775043428101933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186744875850028952067955 280117313775043428101933)
          ·
            refine ⟨105043992665641285538225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280117313775043428101933 105043992665641285538225)
            ·
              refine ⟨78782994499230964153669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105043992665641285538225 78782994499230964153669)
              ·
                refine ⟨14771811468605805778813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78782994499230964153669 14771811468605805778813)
                ·
                  rfl

theorem cell19_48546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_48546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48546 prefixEnd_48546 := by exact prefixLift 48546
  have htrace : WordTrace (prefixWord ++ tailWord_48546) baseStart_48546 baseEnd_48546 := by
    simpa [prefixWord, tailWord_48546, baseEnd_48546] using wordTrace_append hprefix tailTrace_48546
  have hstable : (prefixWord ++ tailWord_48546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48546).length < 2 ^ (prefixWord ++ tailWord_48546).sum := by decide
  have hdescent : baseEnd_48546 < baseStart_48546 := by decide
  rcases family_descends (prefixWord ++ tailWord_48546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48578 : List Nat := [3, 5, 2, 1, 2, 6]
def baseStart_48578 : Nat := 118140960795 + 48578 * 2 ^ 59
def prefixEnd_48578 : Nat := 4983230072969 + 3 ^ 40 * 48578 * 2
def baseEnd_48578 : Nat := 1642394287026579229735

theorem tailTrace_48578 : CollatzResearch.WordTrace tailWord_48578 prefixEnd_48578 1642394287026579229735 := by
  unfold tailWord_48578
  simp only [CollatzResearch.WordTrace]
  refine ⟨442946304504419326748597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1181190145345118204662925 442946304504419326748597)
  ·
    refine ⟨41526216047289311882681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 442946304504419326748597 41526216047289311882681)
    ·
      refine ⟨31144662035466983912011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41526216047289311882681 31144662035466983912011)
      ·
        refine ⟨46716993053200475868017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31144662035466983912011 46716993053200475868017)
        ·
          refine ⟨35037744789900356901013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46716993053200475868017 35037744789900356901013)
          ·
            refine ⟨1642394287026579229735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35037744789900356901013 1642394287026579229735)
            ·
              rfl

theorem cell19_48578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 6].length) (baseStart_48578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48578 prefixEnd_48578 := by exact prefixLift 48578
  have htrace : WordTrace (prefixWord ++ tailWord_48578) baseStart_48578 baseEnd_48578 := by
    simpa [prefixWord, tailWord_48578, baseEnd_48578] using wordTrace_append hprefix tailTrace_48578
  have hstable : (prefixWord ++ tailWord_48578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48578).length < 2 ^ (prefixWord ++ tailWord_48578).sum := by decide
  have hdescent : baseEnd_48578 < baseStart_48578 := by decide
  rcases family_descends (prefixWord ++ tailWord_48578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48622 : List Nat := [4, 1, 2, 1, 2, 1, 5, 3]
def baseStart_48622 : Nat := 118140960795 + 48622 * 2 ^ 59
def prefixEnd_48622 : Nat := 4983230072969 + 3 ^ 40 * 48622 * 2
def baseEnd_48622 : Nat := 14794937115860148089717

theorem tailTrace_48622 : CollatzResearch.WordTrace tailWord_48622 prefixEnd_48622 14794937115860148089717 := by
  unfold tailWord_48622
  simp only [CollatzResearch.WordTrace]
  refine ⟨221673753732284102699515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1182260019905515214397413 221673753732284102699515)
  ·
    refine ⟨332510630598426154049273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221673753732284102699515 332510630598426154049273)
    ·
      refine ⟨249382972948819615536955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332510630598426154049273 249382972948819615536955)
      ·
        refine ⟨374074459423229423305433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249382972948819615536955 374074459423229423305433)
        ·
          refine ⟨280555844567422067479075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374074459423229423305433 280555844567422067479075)
          ·
            refine ⟨420833766851133101218613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280555844567422067479075 420833766851133101218613)
            ·
              refine ⟨39453165642293728239245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 420833766851133101218613 39453165642293728239245)
              ·
                refine ⟨14794937115860148089717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39453165642293728239245 14794937115860148089717)
                ·
                  rfl

theorem cell19_48622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_48622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48622 prefixEnd_48622 := by exact prefixLift 48622
  have htrace : WordTrace (prefixWord ++ tailWord_48622) baseStart_48622 baseEnd_48622 := by
    simpa [prefixWord, tailWord_48622, baseEnd_48622] using wordTrace_append hprefix tailTrace_48622
  have hstable : (prefixWord ++ tailWord_48622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48622).length < 2 ^ (prefixWord ++ tailWord_48622).sum := by decide
  have hdescent : baseEnd_48622 < baseStart_48622 := by decide
  rcases family_descends (prefixWord ++ tailWord_48622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48757 : List Nat := [1, 3, 4, 2, 1, 8]
def baseStart_48757 : Nat := 118140960795 + 48757 * 2 ^ 59
def prefixEnd_48757 : Nat := 4983230072969 + 3 ^ 40 * 48757 * 2
def baseEnd_48757 : Nat := 1648446174246648343261

theorem tailTrace_48757 : CollatzResearch.WordTrace tailWord_48757 prefixEnd_48757 1648446174246648343261 := by
  unfold tailWord_48757
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778313884369190877760525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1185542589579460585173683 1778313884369190877760525)
  ·
    refine ⟨666867706638446579160197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1778313884369190877760525 666867706638446579160197)
    ·
      refine ⟨125037694994708733592537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 666867706638446579160197 125037694994708733592537)
      ·
        refine ⟨93778271246031550194403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125037694994708733592537 93778271246031550194403)
        ·
          refine ⟨140667406869047325291605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93778271246031550194403 140667406869047325291605)
          ·
            refine ⟨1648446174246648343261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 140667406869047325291605 1648446174246648343261)
            ·
              rfl

theorem cell19_48757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 8].length) (baseStart_48757 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48757 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48757 prefixEnd_48757 := by exact prefixLift 48757
  have htrace : WordTrace (prefixWord ++ tailWord_48757) baseStart_48757 baseEnd_48757 := by
    simpa [prefixWord, tailWord_48757, baseEnd_48757] using wordTrace_append hprefix tailTrace_48757
  have hstable : (prefixWord ++ tailWord_48757).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48757).length < 2 ^ (prefixWord ++ tailWord_48757).sum := by decide
  have hdescent : baseEnd_48757 < baseStart_48757 := by decide
  rcases family_descends (prefixWord ++ tailWord_48757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48772 : List Nat := [2, 3, 2, 1, 5, 1, 1, 4]
def baseStart_48772 : Nat := 118140960795 + 48772 * 2 ^ 59
def prefixEnd_48772 : Nat := 4983230072969 + 3 ^ 40 * 48772 * 2
def baseEnd_48772 : Nat := 14840579840704244755975

theorem tailTrace_48772 : CollatzResearch.WordTrace tailWord_48772 prefixEnd_48772 14840579840704244755975 := by
  unfold tailWord_48772
  simp only [CollatzResearch.WordTrace]
  refine ⟨889430489657424219778285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1185907319543232293037713 889430489657424219778285)
  ·
    refine ⟨333536433621534082416857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 889430489657424219778285 333536433621534082416857)
    ·
      refine ⟨250152325216150561812643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333536433621534082416857 250152325216150561812643)
      ·
        refine ⟨375228487824225842718965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250152325216150561812643 375228487824225842718965)
        ·
          refine ⟨35177670733521172754903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 375228487824225842718965 35177670733521172754903)
          ·
            refine ⟨52766506100281759132355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35177670733521172754903 52766506100281759132355)
            ·
              refine ⟨79149759150422638698533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52766506100281759132355 79149759150422638698533)
              ·
                refine ⟨14840579840704244755975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79149759150422638698533 14840579840704244755975)
                ·
                  rfl

theorem cell19_48772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_48772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48772 prefixEnd_48772 := by exact prefixLift 48772
  have htrace : WordTrace (prefixWord ++ tailWord_48772) baseStart_48772 baseEnd_48772 := by
    simpa [prefixWord, tailWord_48772, baseEnd_48772] using wordTrace_append hprefix tailTrace_48772
  have hstable : (prefixWord ++ tailWord_48772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48772).length < 2 ^ (prefixWord ++ tailWord_48772).sum := by decide
  have hdescent : baseEnd_48772 < baseStart_48772 := by decide
  rcases family_descends (prefixWord ++ tailWord_48772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48850 : List Nat := [3, 2, 2, 2, 2, 1, 4, 3]
def baseStart_48850 : Nat := 118140960795 + 48850 * 2 ^ 59
def prefixEnd_48850 : Nat := 4983230072969 + 3 ^ 40 * 48850 * 2
def baseEnd_48850 : Nat := 14864314057623175022429

theorem tailTrace_48850 : CollatzResearch.WordTrace tailWord_48850 prefixEnd_48850 14864314057623175022429 := by
  unfold tailWord_48850
  simp only [CollatzResearch.WordTrace]
  refine ⟨445426468258066940224001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1187803915354845173930669 445426468258066940224001)
  ·
    refine ⟨334069851193550205168001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 445426468258066940224001 334069851193550205168001)
    ·
      refine ⟨250552388395162653876001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334069851193550205168001 250552388395162653876001)
      ·
        refine ⟨187914291296371990407001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250552388395162653876001 187914291296371990407001)
        ·
          refine ⟨140935718472278992805251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187914291296371990407001 140935718472278992805251)
          ·
            refine ⟨211403577708418489207877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140935718472278992805251 211403577708418489207877)
            ·
              refine ⟨39638170820328466726477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211403577708418489207877 39638170820328466726477)
              ·
                refine ⟨14864314057623175022429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39638170820328466726477 14864314057623175022429)
                ·
                  rfl

theorem cell19_48850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_48850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48850 prefixEnd_48850 := by exact prefixLift 48850
  have htrace : WordTrace (prefixWord ++ tailWord_48850) baseStart_48850 baseEnd_48850 := by
    simpa [prefixWord, tailWord_48850, baseEnd_48850] using wordTrace_append hprefix tailTrace_48850
  have hstable : (prefixWord ++ tailWord_48850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48850).length < 2 ^ (prefixWord ++ tailWord_48850).sum := by decide
  have hdescent : baseEnd_48850 < baseStart_48850 := by decide
  rcases family_descends (prefixWord ++ tailWord_48850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48926 : List Nat := [4, 3, 2, 2, 8]
def baseStart_48926 : Nat := 118140960795 + 48926 * 2 ^ 59
def prefixEnd_48926 : Nat := 4983230072969 + 3 ^ 40 * 48926 * 2
def baseEnd_48926 : Nat := 551386655736204345679

theorem tailTrace_48926 : CollatzResearch.WordTrace tailWord_48926 prefixEnd_48926 551386655736204345679 := by
  unfold tailWord_48926
  simp only [CollatzResearch.WordTrace]
  refine ⟨223059727594616592582829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1189651880504621827108421 223059727594616592582829)
  ·
    refine ⟨83647397847981222218561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 223059727594616592582829 83647397847981222218561)
    ·
      refine ⟨62735548385985916663921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83647397847981222218561 62735548385985916663921)
      ·
        refine ⟨47051661289489437497941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62735548385985916663921 47051661289489437497941)
        ·
          refine ⟨551386655736204345679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 47051661289489437497941 551386655736204345679)
          ·
            rfl

theorem cell19_48926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 8].length) (baseStart_48926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_48926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_48926 prefixEnd_48926 := by exact prefixLift 48926
  have htrace : WordTrace (prefixWord ++ tailWord_48926) baseStart_48926 baseEnd_48926 := by
    simpa [prefixWord, tailWord_48926, baseEnd_48926] using wordTrace_append hprefix tailTrace_48926
  have hstable : (prefixWord ++ tailWord_48926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48926).length < 2 ^ (prefixWord ++ tailWord_48926).sum := by decide
  have hdescent : baseEnd_48926 < baseStart_48926 := by decide
  rcases family_descends (prefixWord ++ tailWord_48926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49038 : List Nat := [4, 1, 1, 5, 2, 1, 5]
def baseStart_49038 : Nat := 118140960795 + 49038 * 2 ^ 59
def prefixEnd_49038 : Nat := 4983230072969 + 3 ^ 40 * 49038 * 2
def baseEnd_49038 : Nat := 4973839868698147614713

theorem tailTrace_49038 : CollatzResearch.WordTrace tailWord_49038 prefixEnd_49038 4973839868698147614713 := by
  unfold tailWord_49038
  simp only [CollatzResearch.WordTrace]
  refine ⟨223570349543896983592471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1192375197567450579159845 223570349543896983592471)
  ·
    refine ⟨335355524315845475388707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223570349543896983592471 335355524315845475388707)
    ·
      refine ⟨503033286473768213083061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335355524315845475388707 503033286473768213083061)
      ·
        refine ⟨47159370606915769976537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 503033286473768213083061 47159370606915769976537)
        ·
          refine ⟨35369527955186827482403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47159370606915769976537 35369527955186827482403)
          ·
            refine ⟨53054291932780241223605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35369527955186827482403 53054291932780241223605)
            ·
              refine ⟨4973839868698147614713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53054291932780241223605 4973839868698147614713)
              ·
                rfl

theorem cell19_49038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 5].length) (baseStart_49038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49038 prefixEnd_49038 := by exact prefixLift 49038
  have htrace : WordTrace (prefixWord ++ tailWord_49038) baseStart_49038 baseEnd_49038 := by
    simpa [prefixWord, tailWord_49038, baseEnd_49038] using wordTrace_append hprefix tailTrace_49038
  have hstable : (prefixWord ++ tailWord_49038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49038).length < 2 ^ (prefixWord ++ tailWord_49038).sum := by decide
  have hdescent : baseEnd_49038 < baseStart_49038 := by decide
  rcases family_descends (prefixWord ++ tailWord_49038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49042 : List Nat := [3, 2, 3, 2, 1, 1, 7]
def baseStart_49042 : Nat := 118140960795 + 49042 * 2 ^ 59
def prefixEnd_49042 : Nat := 4983230072969 + 3 ^ 40 * 49042 * 2
def baseEnd_49042 : Nat := 4974245581807872918413

theorem tailTrace_49042 : CollatzResearch.WordTrace tailWord_49042 prefixEnd_49042 4974245581807872918413 := by
  unfold tailWord_49042
  simp only [CollatzResearch.WordTrace]
  refine ⟨447177172084171137971345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1192472458891123034590253 447177172084171137971345)
  ·
    refine ⟨335382879063128353478509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 447177172084171137971345 335382879063128353478509)
    ·
      refine ⟨125768579648673132554441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335382879063128353478509 125768579648673132554441)
      ·
        refine ⟨94326434736504849415831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125768579648673132554441 94326434736504849415831)
        ·
          refine ⟨141489652104757274123747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94326434736504849415831 141489652104757274123747)
          ·
            refine ⟨212234478157135911185621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141489652104757274123747 212234478157135911185621)
            ·
              refine ⟨4974245581807872918413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 212234478157135911185621 4974245581807872918413)
              ·
                rfl

theorem cell19_49042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_49042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49042 prefixEnd_49042 := by exact prefixLift 49042
  have htrace : WordTrace (prefixWord ++ tailWord_49042) baseStart_49042 baseEnd_49042 := by
    simpa [prefixWord, tailWord_49042, baseEnd_49042] using wordTrace_append hprefix tailTrace_49042
  have hstable : (prefixWord ++ tailWord_49042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49042).length < 2 ^ (prefixWord ++ tailWord_49042).sum := by decide
  have hdescent : baseEnd_49042 < baseStart_49042 := by decide
  rcases family_descends (prefixWord ++ tailWord_49042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49133 : List Nat := [1, 5, 1, 4, 1, 1, 3, 3]
def baseStart_49133 : Nat := 118140960795 + 49133 * 2 ^ 59
def prefixEnd_49133 : Nat := 4983230072969 + 3 ^ 40 * 49133 * 2
def baseEnd_49133 : Nat := 14950426665162370732769

theorem tailTrace_49133 : CollatzResearch.WordTrace tailWord_49133 prefixEnd_49133 14950426665162370732769 := by
  unfold tailWord_49133
  simp only [CollatzResearch.WordTrace]
  refine ⟨1792027731007007093448053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1194685154004671395632035 1792027731007007093448053)
  ·
    refine ⟨168002599781906915010755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1792027731007007093448053 168002599781906915010755)
    ·
      refine ⟨252003899672860372516133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168002599781906915010755 252003899672860372516133)
      ·
        refine ⟨47250731188661319846775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252003899672860372516133 47250731188661319846775)
        ·
          refine ⟨70876096782991979770163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47250731188661319846775 70876096782991979770163)
          ·
            refine ⟨106314145174487969655245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70876096782991979770163 106314145174487969655245)
            ·
              refine ⟨39867804440432988620717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106314145174487969655245 39867804440432988620717)
              ·
                refine ⟨14950426665162370732769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39867804440432988620717 14950426665162370732769)
                ·
                  rfl

theorem cell19_49133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_49133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49133 prefixEnd_49133 := by exact prefixLift 49133
  have htrace : WordTrace (prefixWord ++ tailWord_49133) baseStart_49133 baseEnd_49133 := by
    simpa [prefixWord, tailWord_49133, baseEnd_49133] using wordTrace_append hprefix tailTrace_49133
  have hstable : (prefixWord ++ tailWord_49133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49133).length < 2 ^ (prefixWord ++ tailWord_49133).sum := by decide
  have hdescent : baseEnd_49133 < baseStart_49133 := by decide
  rcases family_descends (prefixWord ++ tailWord_49133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49192 : List Nat := [2, 1, 5, 3, 1, 1, 1, 5]
def baseStart_49192 : Nat := 118140960795 + 49192 * 2 ^ 59
def prefixEnd_49192 : Nat := 4983230072969 + 3 ^ 40 * 49192 * 2
def baseEnd_49192 : Nat := 14968379470267715421497

theorem tailTrace_49192 : CollatzResearch.WordTrace tailWord_49192 prefixEnd_49192 14968379470267715421497 := by
  unfold tailWord_49192
  simp only [CollatzResearch.WordTrace]
  refine ⟨897089818896630084922915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1196119758528840113230553 897089818896630084922915)
  ·
    refine ⟨1345634728344945127384373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 897089818896630084922915 1345634728344945127384373)
    ·
      refine ⟨126153255782338605692285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1345634728344945127384373 126153255782338605692285)
      ·
        refine ⟨47307470918376977134607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126153255782338605692285 47307470918376977134607)
        ·
          refine ⟨70961206377565465701911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47307470918376977134607 70961206377565465701911)
          ·
            refine ⟨106441809566348198552867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70961206377565465701911 106441809566348198552867)
            ·
              refine ⟨159662714349522297829301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106441809566348198552867 159662714349522297829301)
              ·
                refine ⟨14968379470267715421497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159662714349522297829301 14968379470267715421497)
                ·
                  rfl

theorem cell19_49192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_49192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49192 prefixEnd_49192 := by exact prefixLift 49192
  have htrace : WordTrace (prefixWord ++ tailWord_49192) baseStart_49192 baseEnd_49192 := by
    simpa [prefixWord, tailWord_49192, baseEnd_49192] using wordTrace_append hprefix tailTrace_49192
  have hstable : (prefixWord ++ tailWord_49192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49192).length < 2 ^ (prefixWord ++ tailWord_49192).sum := by decide
  have hdescent : baseEnd_49192 < baseStart_49192 := by decide
  rcases family_descends (prefixWord ++ tailWord_49192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49194 : List Nat := [3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_49194 : Nat := 118140960795 + 49194 * 2 ^ 59
def prefixEnd_49194 : Nat := 4983230072969 + 3 ^ 40 * 49194 * 2
def baseEnd_49194 : Nat := 14968988039932303377047

theorem tailTrace_49194 : CollatzResearch.WordTrace tailWord_49194 prefixEnd_49194 14968988039932303377047 := by
  unfold tailWord_49194
  simp only [CollatzResearch.WordTrace]
  refine ⟨448563145946503627854659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1196168389190676340945757 448563145946503627854659)
  ·
    refine ⟨672844718919755441781989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 448563145946503627854659 672844718919755441781989)
    ·
      refine ⟨126158384797454145334123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 672844718919755441781989 126158384797454145334123)
      ·
        refine ⟨189237577196181218001185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126158384797454145334123 189237577196181218001185)
        ·
          refine ⟨141928182897135913500889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189237577196181218001185 141928182897135913500889)
          ·
            refine ⟨106446137172851935125667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141928182897135913500889 106446137172851935125667)
            ·
              refine ⟨159669205759277902688501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106446137172851935125667 159669205759277902688501)
              ·
                refine ⟨14968988039932303377047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159669205759277902688501 14968988039932303377047)
                ·
                  rfl

theorem cell19_49194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_49194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49194 prefixEnd_49194 := by exact prefixLift 49194
  have htrace : WordTrace (prefixWord ++ tailWord_49194) baseStart_49194 baseEnd_49194 := by
    simpa [prefixWord, tailWord_49194, baseEnd_49194] using wordTrace_append hprefix tailTrace_49194
  have hstable : (prefixWord ++ tailWord_49194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49194).length < 2 ^ (prefixWord ++ tailWord_49194).sum := by decide
  have hdescent : baseEnd_49194 < baseStart_49194 := by decide
  rcases family_descends (prefixWord ++ tailWord_49194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49253 : List Nat := [1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_49253 : Nat := 118140960795 + 49253 * 2 ^ 59
def prefixEnd_49253 : Nat := 4983230072969 + 3 ^ 40 * 49253 * 2
def baseEnd_49253 : Nat := 14986940845037648065775

theorem tailTrace_49253 : CollatzResearch.WordTrace tailWord_49253 prefixEnd_49253 14986940845037648065775 := by
  unfold tailWord_49253
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796404490572267587816413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1197602993714845058544275 1796404490572267587816413)
  ·
    refine ⟨673651683964600345431155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1796404490572267587816413 673651683964600345431155)
    ·
      refine ⟨1010477525946900518146733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 673651683964600345431155 1010477525946900518146733)
      ·
        refine ⟨378929072230087694305025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1010477525946900518146733 378929072230087694305025)
        ·
          refine ⟨284196804172565770728769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378929072230087694305025 284196804172565770728769)
          ·
            refine ⟨213147603129424328046577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284196804172565770728769 213147603129424328046577)
            ·
              refine ⟨159860702347068246034933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213147603129424328046577 159860702347068246034933)
              ·
                refine ⟨14986940845037648065775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159860702347068246034933 14986940845037648065775)
                ·
                  rfl

theorem cell19_49253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_49253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49253 prefixEnd_49253 := by exact prefixLift 49253
  have htrace : WordTrace (prefixWord ++ tailWord_49253) baseStart_49253 baseEnd_49253 := by
    simpa [prefixWord, tailWord_49253, baseEnd_49253] using wordTrace_append hprefix tailTrace_49253
  have hstable : (prefixWord ++ tailWord_49253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49253).length < 2 ^ (prefixWord ++ tailWord_49253).sum := by decide
  have hdescent : baseEnd_49253 < baseStart_49253 := by decide
  rcases family_descends (prefixWord ++ tailWord_49253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49306 : List Nat := [3, 1, 1, 5, 2, 1, 3, 3]
def baseStart_49306 : Nat := 118140960795 + 49306 * 2 ^ 59
def prefixEnd_49306 : Nat := 4983230072969 + 3 ^ 40 * 49306 * 2
def baseEnd_49306 : Nat := 15003067941149228887853

theorem tailTrace_49306 : CollatzResearch.WordTrace tailWord_49306 prefixEnd_49306 15003067941149228887853 := by
  unfold tailWord_49306
  simp only [CollatzResearch.WordTrace]
  refine ⟨449584389845064409873943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1198891706253505092997181 449584389845064409873943)
  ·
    refine ⟨674376584767596614810915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 449584389845064409873943 674376584767596614810915)
    ·
      refine ⟨1011564877151394922216373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674376584767596614810915 1011564877151394922216373)
      ·
        refine ⟨94834207232943273957785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1011564877151394922216373 94834207232943273957785)
        ·
          refine ⟨71125655424707455468339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94834207232943273957785 71125655424707455468339)
          ·
            refine ⟨106688483137061183202509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71125655424707455468339 106688483137061183202509)
            ·
              refine ⟨40008181176397943700941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106688483137061183202509 40008181176397943700941)
              ·
                refine ⟨15003067941149228887853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40008181176397943700941 15003067941149228887853)
                ·
                  rfl

theorem cell19_49306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_49306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49306 prefixEnd_49306 := by exact prefixLift 49306
  have htrace : WordTrace (prefixWord ++ tailWord_49306) baseStart_49306 baseEnd_49306 := by
    simpa [prefixWord, tailWord_49306, baseEnd_49306] using wordTrace_append hprefix tailTrace_49306
  have hstable : (prefixWord ++ tailWord_49306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49306).length < 2 ^ (prefixWord ++ tailWord_49306).sum := by decide
  have hdescent : baseEnd_49306 < baseStart_49306 := by decide
  rcases family_descends (prefixWord ++ tailWord_49306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49308 : List Nat := [2, 2, 3, 2, 1, 1, 5, 3]
def baseStart_49308 : Nat := 118140960795 + 49308 * 2 ^ 59
def prefixEnd_49308 : Nat := 4983230072969 + 3 ^ 40 * 49308 * 2
def baseEnd_49308 : Nat := 15003676510813816843403

theorem tailTrace_49308 : CollatzResearch.WordTrace tailWord_49308 prefixEnd_49308 15003676510813816843403 := by
  unfold tailWord_49308
  simp only [CollatzResearch.WordTrace]
  refine ⟨899205252686505990534289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1198940336915341320712385 899205252686505990534289)
  ·
    refine ⟨674403939514879492900717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 899205252686505990534289 674403939514879492900717)
    ·
      refine ⟨252901477318079809837769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 674403939514879492900717 252901477318079809837769)
      ·
        refine ⟨189676107988559857378327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252901477318079809837769 189676107988559857378327)
        ·
          refine ⟨284514161982839786067491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189676107988559857378327 284514161982839786067491)
          ·
            refine ⟨426771242974259679101237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284514161982839786067491 426771242974259679101237)
            ·
              refine ⟨40009804028836844915741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 426771242974259679101237 40009804028836844915741)
              ·
                refine ⟨15003676510813816843403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40009804028836844915741 15003676510813816843403)
                ·
                  rfl

theorem cell19_49308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_49308 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49308 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49308 prefixEnd_49308 := by exact prefixLift 49308
  have htrace : WordTrace (prefixWord ++ tailWord_49308) baseStart_49308 baseEnd_49308 := by
    simpa [prefixWord, tailWord_49308, baseEnd_49308] using wordTrace_append hprefix tailTrace_49308
  have hstable : (prefixWord ++ tailWord_49308).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49308).length < 2 ^ (prefixWord ++ tailWord_49308).sum := by decide
  have hdescent : baseEnd_49308 < baseStart_49308 := by decide
  rcases family_descends (prefixWord ++ tailWord_49308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49365 : List Nat := [1, 3, 2, 4, 2, 1, 1, 5]
def baseStart_49365 : Nat := 118140960795 + 49365 * 2 ^ 59
def prefixEnd_49365 : Nat := 4983230072969 + 3 ^ 40 * 49365 * 2
def baseEnd_49365 : Nat := 15021020746254573576581

theorem tailTrace_49365 : CollatzResearch.WordTrace tailWord_49365 prefixEnd_49365 15021020746254573576581 := by
  unfold tailWord_49365
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800489466166510715893549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1200326310777673810595699 1800489466166510715893549)
  ·
    refine ⟨675183549812441518460081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1800489466166510715893549 675183549812441518460081)
    ·
      refine ⟨506387662359331138845061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675183549812441518460081 506387662359331138845061)
      ·
        refine ⟨94947686692374588533449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 506387662359331138845061 94947686692374588533449)
        ·
          refine ⟨71210765019280941400087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94947686692374588533449 71210765019280941400087)
          ·
            refine ⟨106816147528921412100131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71210765019280941400087 106816147528921412100131)
            ·
              refine ⟨160224221293382118150197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106816147528921412100131 160224221293382118150197)
              ·
                refine ⟨15021020746254573576581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160224221293382118150197 15021020746254573576581)
                ·
                  rfl

theorem cell19_49365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_49365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49365 prefixEnd_49365 := by exact prefixLift 49365
  have htrace : WordTrace (prefixWord ++ tailWord_49365) baseStart_49365 baseEnd_49365 := by
    simpa [prefixWord, tailWord_49365, baseEnd_49365] using wordTrace_append hprefix tailTrace_49365
  have hstable : (prefixWord ++ tailWord_49365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49365).length < 2 ^ (prefixWord ++ tailWord_49365).sum := by decide
  have hdescent : baseEnd_49365 < baseStart_49365 := by decide
  rcases family_descends (prefixWord ++ tailWord_49365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49378 : List Nat := [3, 3, 4, 1, 2, 1, 5]
def baseStart_49378 : Nat := 118140960795 + 49378 * 2 ^ 59
def prefixEnd_49378 : Nat := 4983230072969 + 3 ^ 40 * 49378 * 2
def baseEnd_49378 : Nat := 5008325483024798429219

theorem tailTrace_49378 : CollatzResearch.WordTrace tailWord_49378 prefixEnd_49378 5008325483024798429219 := by
  unfold tailWord_49378
  simp only [CollatzResearch.WordTrace]
  refine ⟨450240903779853484029197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1200642410079609290744525 450240903779853484029197)
  ·
    refine ⟨168840338917445056510949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 450240903779853484029197 168840338917445056510949)
    ·
      refine ⟨31657563547020948095803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168840338917445056510949 31657563547020948095803)
      ·
        refine ⟨47486345320531422143705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31657563547020948095803 47486345320531422143705)
        ·
          refine ⟨35614758990398566607779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47486345320531422143705 35614758990398566607779)
          ·
            refine ⟨53422138485597849911669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35614758990398566607779 53422138485597849911669)
            ·
              refine ⟨5008325483024798429219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53422138485597849911669 5008325483024798429219)
              ·
                rfl

theorem cell19_49378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 5].length) (baseStart_49378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49378 prefixEnd_49378 := by exact prefixLift 49378
  have htrace : WordTrace (prefixWord ++ tailWord_49378) baseStart_49378 baseEnd_49378 := by
    simpa [prefixWord, tailWord_49378, baseEnd_49378] using wordTrace_append hprefix tailTrace_49378
  have hstable : (prefixWord ++ tailWord_49378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49378).length < 2 ^ (prefixWord ++ tailWord_49378).sum := by decide
  have hdescent : baseEnd_49378 < baseStart_49378 := by decide
  rcases family_descends (prefixWord ++ tailWord_49378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49445 : List Nat := [1, 3, 1, 2, 12]
def baseStart_49445 : Nat := 118140960795 + 49445 * 2 ^ 59
def prefixEnd_49445 : Nat := 4983230072969 + 3 ^ 40 * 49445 * 2
def baseEnd_49445 : Nat := 557235686401410807355

theorem tailTrace_49445 : CollatzResearch.WordTrace tailWord_49445 prefixEnd_49445 557235686401410807355 := by
  unfold tailWord_49445
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803407305876684378805789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1202271537251122919203859 1803407305876684378805789)
  ·
    refine ⟨676277739703756642052171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1803407305876684378805789 676277739703756642052171)
    ·
      refine ⟨1014416609555634963078257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676277739703756642052171 1014416609555634963078257)
      ·
        refine ⟨760812457166726222308693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1014416609555634963078257 760812457166726222308693)
        ·
          refine ⟨557235686401410807355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 760812457166726222308693 557235686401410807355)
          ·
            rfl

theorem cell19_49445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 12].length) (baseStart_49445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49445 prefixEnd_49445 := by exact prefixLift 49445
  have htrace : WordTrace (prefixWord ++ tailWord_49445) baseStart_49445 baseEnd_49445 := by
    simpa [prefixWord, tailWord_49445, baseEnd_49445] using wordTrace_append hprefix tailTrace_49445
  have hstable : (prefixWord ++ tailWord_49445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49445).length < 2 ^ (prefixWord ++ tailWord_49445).sum := by decide
  have hdescent : baseEnd_49445 < baseStart_49445 := by decide
  rcases family_descends (prefixWord ++ tailWord_49445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49458 : List Nat := [3, 2, 1, 1, 6, 1, 1, 4]
def baseStart_49458 : Nat := 118140960795 + 49458 * 2 ^ 59
def prefixEnd_49458 : Nat := 4983230072969 + 3 ^ 40 * 49458 * 2
def baseEnd_49458 : Nat := 15049319235657913509661

theorem tailTrace_49458 : CollatzResearch.WordTrace tailWord_49458 prefixEnd_49458 15049319235657913509661 := by
  unfold tailWord_49458
  simp only [CollatzResearch.WordTrace]
  refine ⟨450970363707396899757257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1202587636553058399352685 450970363707396899757257)
  ·
    refine ⟨338227772780547674817943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 450970363707396899757257 338227772780547674817943)
    ·
      refine ⟨507341659170821512226915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338227772780547674817943 507341659170821512226915)
      ·
        refine ⟨761012488756232268340373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507341659170821512226915 761012488756232268340373)
        ·
          refine ⟨35672460410448387578455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 761012488756232268340373 35672460410448387578455)
          ·
            refine ⟨53508690615672581367683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35672460410448387578455 53508690615672581367683)
            ·
              refine ⟨80263035923508872051525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53508690615672581367683 80263035923508872051525)
              ·
                refine ⟨15049319235657913509661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80263035923508872051525 15049319235657913509661)
                ·
                  rfl

theorem cell19_49458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_49458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49458 prefixEnd_49458 := by exact prefixLift 49458
  have htrace : WordTrace (prefixWord ++ tailWord_49458) baseStart_49458 baseEnd_49458 := by
    simpa [prefixWord, tailWord_49458, baseEnd_49458] using wordTrace_append hprefix tailTrace_49458
  have hstable : (prefixWord ++ tailWord_49458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49458).length < 2 ^ (prefixWord ++ tailWord_49458).sum := by decide
  have hdescent : baseEnd_49458 < baseStart_49458 := by decide
  rcases family_descends (prefixWord ++ tailWord_49458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49460 : List Nat := [2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_49460 : Nat := 118140960795 + 49460 * 2 ^ 59
def prefixEnd_49460 : Nat := 4983230072969 + 3 ^ 40 * 49460 * 2
def baseEnd_49460 : Nat := 15049927805322501465211

theorem tailTrace_49460 : CollatzResearch.WordTrace tailWord_49460 prefixEnd_49460 15049927805322501465211 := by
  unfold tailWord_49460
  simp only [CollatzResearch.WordTrace]
  refine ⟨901977200411170970300917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1202636267214894627067889 901977200411170970300917)
  ·
    refine ⟨84560362538547278465711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 901977200411170970300917 84560362538547278465711)
    ·
      refine ⟨126840543807820917698567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84560362538547278465711 126840543807820917698567)
      ·
        refine ⟨190260815711731376547851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126840543807820917698567 190260815711731376547851)
        ·
          refine ⟨285391223567597064821777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190260815711731376547851 285391223567597064821777)
          ·
            refine ⟨214043417675697798616333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285391223567597064821777 214043417675697798616333)
            ·
              refine ⟨80266281628386674481125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214043417675697798616333 80266281628386674481125)
              ·
                refine ⟨15049927805322501465211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80266281628386674481125 15049927805322501465211)
                ·
                  rfl

theorem cell19_49460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_49460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49460 prefixEnd_49460 := by exact prefixLift 49460
  have htrace : WordTrace (prefixWord ++ tailWord_49460) baseStart_49460 baseEnd_49460 := by
    simpa [prefixWord, tailWord_49460, baseEnd_49460] using wordTrace_append hprefix tailTrace_49460
  have hstable : (prefixWord ++ tailWord_49460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49460).length < 2 ^ (prefixWord ++ tailWord_49460).sum := by decide
  have hdescent : baseEnd_49460 < baseStart_49460 := by decide
  rcases family_descends (prefixWord ++ tailWord_49460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49521 : List Nat := [1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_49521 : Nat := 118140960795 + 49521 * 2 ^ 59
def prefixEnd_49521 : Nat := 4983230072969 + 3 ^ 40 * 49521 * 2
def baseEnd_49521 : Nat := 15068489180092434109489

theorem tailTrace_49521 : CollatzResearch.WordTrace tailWord_49521 prefixEnd_49521 15068489180092434109489 := by
  unfold tailWord_49521
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806179253601349358572417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1204119502400899572381611 1806179253601349358572417)
  ·
    refine ⟨1354634440201012018929313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1806179253601349358572417 1354634440201012018929313)
    ·
      refine ⟨1015975830150759014196985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1354634440201012018929313 1015975830150759014196985)
      ·
        refine ⟨761981872613069260647739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1015975830150759014196985 761981872613069260647739)
        ·
          refine ⟨1142972808919603890971609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761981872613069260647739 1142972808919603890971609)
          ·
            refine ⟨857229606689702918228707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142972808919603890971609 857229606689702918228707)
            ·
              refine ⟨1285844410034554377343061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857229606689702918228707 1285844410034554377343061)
              ·
                refine ⟨15068489180092434109489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1285844410034554377343061 15068489180092434109489)
                ·
                  rfl

theorem cell19_49521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_49521 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49521 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49521 prefixEnd_49521 := by exact prefixLift 49521
  have htrace : WordTrace (prefixWord ++ tailWord_49521) baseStart_49521 baseEnd_49521 := by
    simpa [prefixWord, tailWord_49521, baseEnd_49521] using wordTrace_append hprefix tailTrace_49521
  have hstable : (prefixWord ++ tailWord_49521).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49521).length < 2 ^ (prefixWord ++ tailWord_49521).sum := by decide
  have hdescent : baseEnd_49521 < baseStart_49521 := by decide
  rcases family_descends (prefixWord ++ tailWord_49521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49559 : List Nat := [1, 1, 3, 3, 1, 1, 9]
def baseStart_49559 : Nat := 118140960795 + 49559 * 2 ^ 59
def prefixEnd_49559 : Nat := 4983230072969 + 3 ^ 40 * 49559 * 2
def baseEnd_49559 : Nat := 5026684001239868421647

theorem tailTrace_49559 : CollatzResearch.WordTrace tailWord_49559 prefixEnd_49559 5026684001239868421647 := by
  unfold tailWord_49559
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807565227463681848455731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1205043484975787898970487 1807565227463681848455731)
  ·
    refine ⟨2711347841195522772683597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1807565227463681848455731 2711347841195522772683597)
    ·
      refine ⟨1016755440448321039756349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2711347841195522772683597 1016755440448321039756349)
      ·
        refine ⟨381283290168120389908631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1016755440448321039756349 381283290168120389908631)
        ·
          refine ⟨571924935252180584862947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381283290168120389908631 571924935252180584862947)
          ·
            refine ⟨857887402878270877294421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571924935252180584862947 857887402878270877294421)
            ·
              refine ⟨5026684001239868421647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 857887402878270877294421 5026684001239868421647)
              ·
                rfl

theorem cell19_49559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_49559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49559 prefixEnd_49559 := by exact prefixLift 49559
  have htrace : WordTrace (prefixWord ++ tailWord_49559) baseStart_49559 baseEnd_49559 := by
    simpa [prefixWord, tailWord_49559, baseEnd_49559] using wordTrace_append hprefix tailTrace_49559
  have hstable : (prefixWord ++ tailWord_49559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49559).length < 2 ^ (prefixWord ++ tailWord_49559).sum := by decide
  have hdescent : baseEnd_49559 < baseStart_49559 := by decide
  rcases family_descends (prefixWord ++ tailWord_49559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49671 : List Nat := [1, 1, 4, 3, 3, 1, 6]
def baseStart_49671 : Nat := 118140960795 + 49671 * 2 ^ 59
def prefixEnd_49671 : Nat := 4983230072969 + 3 ^ 40 * 49671 * 2
def baseEnd_49671 : Nat := 5038043968312176925249

theorem tailTrace_49671 : CollatzResearch.WordTrace tailWord_49671 prefixEnd_49671 5038043968312176925249 := by
  unfold tailWord_49671
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811650203057924976532867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1207766802038616651021911 1811650203057924976532867)
  ·
    refine ⟨2717475304586887464799301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1811650203057924976532867 2717475304586887464799301)
    ·
      refine ⟨509526619610041399649869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2717475304586887464799301 509526619610041399649869)
      ·
        refine ⟨191072482353765524868701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509526619610041399649869 191072482353765524868701)
        ·
          refine ⟨71652180882662071825763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191072482353765524868701 71652180882662071825763)
          ·
            refine ⟨107478271323993107738645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71652180882662071825763 107478271323993107738645)
            ·
              refine ⟨5038043968312176925249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107478271323993107738645 5038043968312176925249)
              ·
                rfl

theorem cell19_49671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_49671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49671 prefixEnd_49671 := by exact prefixLift 49671
  have htrace : WordTrace (prefixWord ++ tailWord_49671) baseStart_49671 baseEnd_49671 := by
    simpa [prefixWord, tailWord_49671, baseEnd_49671] using wordTrace_append hprefix tailTrace_49671
  have hstable : (prefixWord ++ tailWord_49671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49671).length < 2 ^ (prefixWord ++ tailWord_49671).sum := by decide
  have hdescent : baseEnd_49671 < baseStart_49671 := by decide
  rcases family_descends (prefixWord ++ tailWord_49671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49703 : List Nat := [1, 1, 7, 2, 1, 2, 2, 3]
def baseStart_49703 : Nat := 118140960795 + 49703 * 2 ^ 59
def prefixEnd_49703 : Nat := 4983230072969 + 3 ^ 40 * 49703 * 2
def baseEnd_49703 : Nat := 15123869019569938064549

theorem tailTrace_49703 : CollatzResearch.WordTrace tailWord_49703 prefixEnd_49703 15123869019569938064549 := by
  unfold tailWord_49703
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812817338941994441697763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1208544892627996294465175 1812817338941994441697763)
  ·
    refine ⟨2719226008412991662546645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1812817338941994441697763 2719226008412991662546645)
    ·
      refine ⟨63731859572179492090937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2719226008412991662546645 63731859572179492090937)
      ·
        refine ⟨47798894679134619068203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63731859572179492090937 47798894679134619068203)
        ·
          refine ⟨71698342018701928602305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47798894679134619068203 71698342018701928602305)
          ·
            refine ⟨53773756514026446451729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71698342018701928602305 53773756514026446451729)
            ·
              refine ⟨40330317385519834838797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53773756514026446451729 40330317385519834838797)
              ·
                refine ⟨15123869019569938064549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40330317385519834838797 15123869019569938064549)
                ·
                  rfl

theorem cell19_49703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_49703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49703 prefixEnd_49703 := by exact prefixLift 49703
  have htrace : WordTrace (prefixWord ++ tailWord_49703) baseStart_49703 baseEnd_49703 := by
    simpa [prefixWord, tailWord_49703, baseEnd_49703] using wordTrace_append hprefix tailTrace_49703
  have hstable : (prefixWord ++ tailWord_49703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49703).length < 2 ^ (prefixWord ++ tailWord_49703).sum := by decide
  have hdescent : baseEnd_49703 < baseStart_49703 := by decide
  rcases family_descends (prefixWord ++ tailWord_49703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49749 : List Nat := [1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_49749 : Nat := 118140960795 + 49749 * 2 ^ 59
def prefixEnd_49749 : Nat := 4983230072969 + 3 ^ 40 * 49749 * 2
def baseEnd_49749 : Nat := 15137866121855461042201

theorem tailTrace_49749 : CollatzResearch.WordTrace tailWord_49749 prefixEnd_49749 15137866121855461042201 := by
  unfold tailWord_49749
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814495096775344297872301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1209663397850229531914867 1814495096775344297872301)
  ·
    refine ⟨680435661290754111702113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1814495096775344297872301 680435661290754111702113)
    ·
      refine ⟨510326745968065583776585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 680435661290754111702113 510326745968065583776585)
      ·
        refine ⟨382745059476049187832439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510326745968065583776585 382745059476049187832439)
        ·
          refine ⟨574117589214073781748659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382745059476049187832439 574117589214073781748659)
          ·
            refine ⟨861176383821110672622989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574117589214073781748659 861176383821110672622989)
            ·
              refine ⟨322941143932916502233621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 861176383821110672622989 322941143932916502233621)
              ·
                refine ⟨15137866121855461042201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 322941143932916502233621 15137866121855461042201)
                ·
                  rfl

theorem cell19_49749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_49749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49749 prefixEnd_49749 := by exact prefixLift 49749
  have htrace : WordTrace (prefixWord ++ tailWord_49749) baseStart_49749 baseEnd_49749 := by
    simpa [prefixWord, tailWord_49749, baseEnd_49749] using wordTrace_append hprefix tailTrace_49749
  have hstable : (prefixWord ++ tailWord_49749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49749).length < 2 ^ (prefixWord ++ tailWord_49749).sum := by decide
  have hdescent : baseEnd_49749 < baseStart_49749 := by decide
  rcases family_descends (prefixWord ++ tailWord_49749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49802 : List Nat := [3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_49802 : Nat := 118140960795 + 49802 * 2 ^ 59
def prefixEnd_49802 : Nat := 4983230072969 + 3 ^ 40 * 49802 * 2
def baseEnd_49802 : Nat := 15153993217967041864279

theorem tailTrace_49802 : CollatzResearch.WordTrace tailWord_49802 prefixEnd_49802 15153993217967041864279 := by
  unfold tailWord_49802
  simp only [CollatzResearch.WordTrace]
  refine ⟨454107041395833587387915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1210952110388889566367773 454107041395833587387915)
  ·
    refine ⟨681160562093750381081873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454107041395833587387915 681160562093750381081873)
    ·
      refine ⟨510870421570312785811405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 681160562093750381081873 510870421570312785811405)
      ·
        refine ⟨191576408088867294679277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 510870421570312785811405 191576408088867294679277)
        ·
          refine ⟨71841153033325235504729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191576408088867294679277 71841153033325235504729)
          ·
            refine ⟨53880864774993926628547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71841153033325235504729 53880864774993926628547)
            ·
              refine ⟨80821297162490889942821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53880864774993926628547 80821297162490889942821)
              ·
                refine ⟨15153993217967041864279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80821297162490889942821 15153993217967041864279)
                ·
                  rfl

theorem cell19_49802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_49802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49802 prefixEnd_49802 := by exact prefixLift 49802
  have htrace : WordTrace (prefixWord ++ tailWord_49802) baseStart_49802 baseEnd_49802 := by
    simpa [prefixWord, tailWord_49802, baseEnd_49802] using wordTrace_append hprefix tailTrace_49802
  have hstable : (prefixWord ++ tailWord_49802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49802).length < 2 ^ (prefixWord ++ tailWord_49802).sum := by decide
  have hdescent : baseEnd_49802 < baseStart_49802 := by decide
  rcases family_descends (prefixWord ++ tailWord_49802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49876 : List Nat := [2, 4, 1, 3, 2, 2, 2, 3]
def baseStart_49876 : Nat := 118140960795 + 49876 * 2 ^ 59
def prefixEnd_49876 : Nat := 4983230072969 + 3 ^ 40 * 49876 * 2
def baseEnd_49876 : Nat := 15176510295556796219633

theorem tailTrace_49876 : CollatzResearch.WordTrace tailWord_49876 prefixEnd_49876 15176510295556796219633 := by
  unfold tailWord_49876
  simp only [CollatzResearch.WordTrace]
  refine ⟨909563583657622493872741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1212751444876829991830321 909563583657622493872741)
  ·
    refine ⟨170543171935804217601139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 909563583657622493872741 170543171935804217601139)
    ·
      refine ⟨255814757903706326401709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170543171935804217601139 255814757903706326401709)
      ·
        refine ⟨95930534213889872400641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255814757903706326401709 95930534213889872400641)
        ·
          refine ⟨71947900660417404300481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95930534213889872400641 71947900660417404300481)
          ·
            refine ⟨53960925495313053225361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71947900660417404300481 53960925495313053225361)
            ·
              refine ⟨40470694121484789919021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53960925495313053225361 40470694121484789919021)
              ·
                refine ⟨15176510295556796219633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40470694121484789919021 15176510295556796219633)
                ·
                  rfl

theorem cell19_49876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_49876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49876 prefixEnd_49876 := by exact prefixLift 49876
  have htrace : WordTrace (prefixWord ++ tailWord_49876) baseStart_49876 baseEnd_49876 := by
    simpa [prefixWord, tailWord_49876, baseEnd_49876] using wordTrace_append hprefix tailTrace_49876
  have hstable : (prefixWord ++ tailWord_49876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49876).length < 2 ^ (prefixWord ++ tailWord_49876).sum := by decide
  have hdescent : baseEnd_49876 < baseStart_49876 := by decide
  rcases family_descends (prefixWord ++ tailWord_49876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49880 : List Nat := [2, 1, 2, 2, 3, 2, 4, 3]
def baseStart_49880 : Nat := 118140960795 + 49880 * 2 ^ 59
def prefixEnd_49880 : Nat := 4983230072969 + 3 ^ 40 * 49880 * 2
def baseEnd_49880 : Nat := 15177727434885972130733

theorem tailTrace_49880 : CollatzResearch.WordTrace tailWord_49880 prefixEnd_49880 15177727434885972130733 := by
  unfold tailWord_49880
  simp only [CollatzResearch.WordTrace]
  refine ⟨909636529650376835445547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1212848706200502447260729 909636529650376835445547)
  ·
    refine ⟨1364454794475565253168321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 909636529650376835445547 1364454794475565253168321)
    ·
      refine ⟨1023341095856673939876241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1364454794475565253168321 1023341095856673939876241)
      ·
        refine ⟨767505821892505454907181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1023341095856673939876241 767505821892505454907181)
        ·
          refine ⟨287814683209689545590193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767505821892505454907181 287814683209689545590193)
          ·
            refine ⟨215861012407267159192645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287814683209689545590193 215861012407267159192645)
            ·
              refine ⟨40473939826362592348621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215861012407267159192645 40473939826362592348621)
              ·
                refine ⟨15177727434885972130733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40473939826362592348621 15177727434885972130733)
                ·
                  rfl

theorem cell19_49880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_49880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49880 prefixEnd_49880 := by exact prefixLift 49880
  have htrace : WordTrace (prefixWord ++ tailWord_49880) baseStart_49880 baseEnd_49880 := by
    simpa [prefixWord, tailWord_49880, baseEnd_49880] using wordTrace_append hprefix tailTrace_49880
  have hstable : (prefixWord ++ tailWord_49880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49880).length < 2 ^ (prefixWord ++ tailWord_49880).sum := by decide
  have hdescent : baseEnd_49880 < baseStart_49880 := by decide
  rcases family_descends (prefixWord ++ tailWord_49880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49882 : List Nat := [3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_49882 : Nat := 118140960795 + 49882 * 2 ^ 59
def prefixEnd_49882 : Nat := 4983230072969 + 3 ^ 40 * 49882 * 2
def baseEnd_49882 : Nat := 15178336004550560086283

theorem tailTrace_49882 : CollatzResearch.WordTrace tailWord_49882 prefixEnd_49882 15178336004550560086283 := by
  unfold tailWord_49882
  simp only [CollatzResearch.WordTrace]
  refine ⟨454836501323377003115975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1212897336862338674975933 454836501323377003115975)
  ·
    refine ⟨682254751985065504673963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454836501323377003115975 682254751985065504673963)
    ·
      refine ⟨1023382127977598257010945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682254751985065504673963 1023382127977598257010945)
      ·
        refine ⟨767536595983198692758209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1023382127977598257010945 767536595983198692758209)
        ·
          refine ⟨575652446987399019568657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767536595983198692758209 575652446987399019568657)
          ·
            refine ⟨431739335240549264676493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575652446987399019568657 431739335240549264676493)
            ·
              refine ⟨161902250715205974253685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 431739335240549264676493 161902250715205974253685)
              ·
                refine ⟨15178336004550560086283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161902250715205974253685 15178336004550560086283)
                ·
                  rfl

theorem cell19_49882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_49882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49882 prefixEnd_49882 := by exact prefixLift 49882
  have htrace : WordTrace (prefixWord ++ tailWord_49882) baseStart_49882 baseEnd_49882 := by
    simpa [prefixWord, tailWord_49882, baseEnd_49882] using wordTrace_append hprefix tailTrace_49882
  have hstable : (prefixWord ++ tailWord_49882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49882).length < 2 ^ (prefixWord ++ tailWord_49882).sum := by decide
  have hdescent : baseEnd_49882 < baseStart_49882 := by decide
  rcases family_descends (prefixWord ++ tailWord_49882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49918 : List Nat := [4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_49918 : Nat := 118140960795 + 49918 * 2 ^ 59
def prefixEnd_49918 : Nat := 4983230072969 + 3 ^ 40 * 49918 * 2
def baseEnd_49918 : Nat := 15189290258513143286185

theorem tailTrace_49918 : CollatzResearch.WordTrace tailWord_49918 prefixEnd_49918 15189290258513143286185 := by
  unfold tailWord_49918
  simp only [CollatzResearch.WordTrace]
  refine ⟨227582379145385770096801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1213772688775390773849605 227582379145385770096801)
  ·
    refine ⟨170686784359039327572601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227582379145385770096801 170686784359039327572601)
    ·
      refine ⟨128015088269279495679451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170686784359039327572601 128015088269279495679451)
      ·
        refine ⟨192022632403919243519177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128015088269279495679451 192022632403919243519177)
        ·
          refine ⟨144016974302939432639383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192022632403919243519177 144016974302939432639383)
          ·
            refine ⟨216025461454409148959075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144016974302939432639383 216025461454409148959075)
            ·
              refine ⟨324038192181613723438613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216025461454409148959075 324038192181613723438613)
              ·
                refine ⟨15189290258513143286185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 324038192181613723438613 15189290258513143286185)
                ·
                  rfl

theorem cell19_49918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_49918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49918 prefixEnd_49918 := by exact prefixLift 49918
  have htrace : WordTrace (prefixWord ++ tailWord_49918) baseStart_49918 baseEnd_49918 := by
    simpa [prefixWord, tailWord_49918, baseEnd_49918] using wordTrace_append hprefix tailTrace_49918
  have hstable : (prefixWord ++ tailWord_49918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49918).length < 2 ^ (prefixWord ++ tailWord_49918).sum := by decide
  have hdescent : baseEnd_49918 < baseStart_49918 := by decide
  rcases family_descends (prefixWord ++ tailWord_49918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49956 : List Nat := [2, 3, 1, 3, 4, 6]
def baseStart_49956 : Nat := 118140960795 + 49956 * 2 ^ 59
def prefixEnd_49956 : Nat := 4983230072969 + 3 ^ 40 * 49956 * 2
def baseEnd_49956 : Nat := 1688983675793368271293

theorem tailTrace_49956 : CollatzResearch.WordTrace tailWord_49956 prefixEnd_49956 1688983675793368271293 := by
  unfold tailWord_49956
  simp only [CollatzResearch.WordTrace]
  refine ⟨911022503512709325328861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1214696671350279100438481 911022503512709325328861)
  ·
    refine ⟨341633438817265996998323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 911022503512709325328861 341633438817265996998323)
    ·
      refine ⟨512450158225898995497485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341633438817265996998323 512450158225898995497485)
      ·
        refine ⟨192168809334712123311557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 512450158225898995497485 192168809334712123311557)
        ·
          refine ⟨36031651750258523120917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192168809334712123311557 36031651750258523120917)
          ·
            refine ⟨1688983675793368271293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36031651750258523120917 1688983675793368271293)
            ·
              rfl

theorem cell19_49956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 6].length) (baseStart_49956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_49956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_49956 prefixEnd_49956 := by exact prefixLift 49956
  have htrace : WordTrace (prefixWord ++ tailWord_49956) baseStart_49956 baseEnd_49956 := by
    simpa [prefixWord, tailWord_49956, baseEnd_49956] using wordTrace_append hprefix tailTrace_49956
  have hstable : (prefixWord ++ tailWord_49956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49956).length < 2 ^ (prefixWord ++ tailWord_49956).sum := by decide
  have hdescent : baseEnd_49956 < baseStart_49956 := by decide
  rcases family_descends (prefixWord ++ tailWord_49956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50053 : List Nat := [1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_50053 : Nat := 118140960795 + 50053 * 2 ^ 59
def prefixEnd_50053 : Nat := 4983230072969 + 3 ^ 40 * 50053 * 2
def baseEnd_50053 : Nat := 15230368710872830285817

theorem tailTrace_50053 : CollatzResearch.WordTrace tailWord_50053 prefixEnd_50053 15230368710872830285817 := by
  unfold tailWord_50053
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825582887674004216938813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1217055258449336144625875 1825582887674004216938813)
  ·
    refine ⟨684593582877751581352055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1825582887674004216938813 684593582877751581352055)
    ·
      refine ⟨1026890374316627372028083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684593582877751581352055 1026890374316627372028083)
      ·
        refine ⟨1540335561474941058042125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026890374316627372028083 1540335561474941058042125)
        ·
          refine ⟨577625835553102896765797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1540335561474941058042125 577625835553102896765797)
          ·
            refine ⟨108304844166206793143587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 577625835553102896765797 108304844166206793143587)
            ·
              refine ⟨162457266249310189715381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108304844166206793143587 162457266249310189715381)
              ·
                refine ⟨15230368710872830285817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162457266249310189715381 15230368710872830285817)
                ·
                  rfl

theorem cell19_50053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_50053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50053 prefixEnd_50053 := by exact prefixLift 50053
  have htrace : WordTrace (prefixWord ++ tailWord_50053) baseStart_50053 baseEnd_50053 := by
    simpa [prefixWord, tailWord_50053, baseEnd_50053] using wordTrace_append hprefix tailTrace_50053
  have hstable : (prefixWord ++ tailWord_50053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50053).length < 2 ^ (prefixWord ++ tailWord_50053).sum := by decide
  have hdescent : baseEnd_50053 < baseStart_50053 := by decide
  rcases family_descends (prefixWord ++ tailWord_50053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50110 : List Nat := [4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_50110 : Nat := 118140960795 + 50110 * 2 ^ 59
def prefixEnd_50110 : Nat := 4983230072969 + 3 ^ 40 * 50110 * 2
def baseEnd_50110 : Nat := 15247712946313587018995

theorem tailTrace_50110 : CollatzResearch.WordTrace tailWord_50110 prefixEnd_50110 15247712946313587018995 := by
  unfold tailWord_50110
  simp only [CollatzResearch.WordTrace]
  refine ⟨228457731058437868970473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1218441232311668634509189 228457731058437868970473)
  ·
    refine ⟨171343298293828401727855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228457731058437868970473 171343298293828401727855)
    ·
      refine ⟨257014947440742602591783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171343298293828401727855 257014947440742602591783)
      ·
        refine ⟨385522421161113903887675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257014947440742602591783 385522421161113903887675)
        ·
          refine ⟨578283631741670855831513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385522421161113903887675 578283631741670855831513)
          ·
            refine ⟨433712723806253141873635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578283631741670855831513 433712723806253141873635)
            ·
              refine ⟨650569085709379712810453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433712723806253141873635 650569085709379712810453)
              ·
                refine ⟨15247712946313587018995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 650569085709379712810453 15247712946313587018995)
                ·
                  rfl

theorem cell19_50110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_50110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50110 prefixEnd_50110 := by exact prefixLift 50110
  have htrace : WordTrace (prefixWord ++ tailWord_50110) baseStart_50110 baseEnd_50110 := by
    simpa [prefixWord, tailWord_50110, baseEnd_50110] using wordTrace_append hprefix tailTrace_50110
  have hstable : (prefixWord ++ tailWord_50110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50110).length < 2 ^ (prefixWord ++ tailWord_50110).sum := by decide
  have hdescent : baseEnd_50110 < baseStart_50110 := by decide
  rcases family_descends (prefixWord ++ tailWord_50110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50125 : List Nat := [1, 6, 3, 1, 8]
def baseStart_50125 : Nat := 118140960795 + 50125 * 2 ^ 59
def prefixEnd_50125 : Nat := 4983230072969 + 3 ^ 40 * 50125 * 2
def baseEnd_50125 : Nat := 564899156251777655023

theorem tailTrace_50125 : CollatzResearch.WordTrace tailWord_50125 prefixEnd_50125 564899156251777655023 := by
  unfold tailWord_50125
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828208943413160513559829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1218805962275440342373219 1828208943413160513559829)
  ·
    refine ⟨85697294222491899073117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1828208943413160513559829 85697294222491899073117)
    ·
      refine ⟨32136485333434462152419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85697294222491899073117 32136485333434462152419)
      ·
        refine ⟨48204728000151693228629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32136485333434462152419 48204728000151693228629)
        ·
          refine ⟨564899156251777655023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 48204728000151693228629 564899156251777655023)
          ·
            rfl

theorem cell19_50125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 8].length) (baseStart_50125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50125 prefixEnd_50125 := by exact prefixLift 50125
  have htrace : WordTrace (prefixWord ++ tailWord_50125) baseStart_50125 baseEnd_50125 := by
    simpa [prefixWord, tailWord_50125, baseEnd_50125] using wordTrace_append hprefix tailTrace_50125
  have hstable : (prefixWord ++ tailWord_50125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50125).length < 2 ^ (prefixWord ++ tailWord_50125).sum := by decide
  have hdescent : baseEnd_50125 < baseStart_50125 := by decide
  rcases family_descends (prefixWord ++ tailWord_50125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50186 : List Nat := [3, 1, 2, 2, 3, 2, 6]
def baseStart_50186 : Nat := 118140960795 + 50186 * 2 ^ 59
def prefixEnd_50186 : Nat := 4983230072969 + 3 ^ 40 * 50186 * 2
def baseEnd_50186 : Nat := 5090279531189309776633

theorem tailTrace_50186 : CollatzResearch.WordTrace tailWord_50186 prefixEnd_50186 5090279531189309776633 := by
  unfold tailWord_50186
  simp only [CollatzResearch.WordTrace]
  refine ⟨457608449048041982882603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1220289197461445287686941 457608449048041982882603)
  ·
    refine ⟨686412673572062974323905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 457608449048041982882603 686412673572062974323905)
    ·
      refine ⟨514809505179047230742929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 686412673572062974323905 514809505179047230742929)
      ·
        refine ⟨386107128884285423057197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514809505179047230742929 386107128884285423057197)
        ·
          refine ⟨144790173331607033646449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386107128884285423057197 144790173331607033646449)
          ·
            refine ⟨108592629998705275234837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144790173331607033646449 108592629998705275234837)
            ·
              refine ⟨5090279531189309776633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108592629998705275234837 5090279531189309776633)
              ·
                rfl

theorem cell19_50186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_50186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50186 prefixEnd_50186 := by exact prefixLift 50186
  have htrace : WordTrace (prefixWord ++ tailWord_50186) baseStart_50186 baseEnd_50186 := by
    simpa [prefixWord, tailWord_50186, baseEnd_50186] using wordTrace_append hprefix tailTrace_50186
  have hstable : (prefixWord ++ tailWord_50186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50186).length < 2 ^ (prefixWord ++ tailWord_50186).sum := by decide
  have hdescent : baseEnd_50186 < baseStart_50186 := by decide
  rcases family_descends (prefixWord ++ tailWord_50186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50218 : List Nat := [3, 1, 4, 1, 4, 1, 2, 3]
def baseStart_50218 : Nat := 118140960795 + 50218 * 2 ^ 59
def prefixEnd_50218 : Nat := 4983230072969 + 3 ^ 40 * 50218 * 2
def baseEnd_50218 : Nat := 15280575708201336618701

theorem tailTrace_50218 : CollatzResearch.WordTrace tailWord_50218 prefixEnd_50218 15280575708201336618701 := by
  unfold tailWord_50218
  simp only [CollatzResearch.WordTrace]
  refine ⟨457900233019059349173827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1221067288050824931130205 457900233019059349173827)
  ·
    refine ⟨686850349528589023760741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 457900233019059349173827 686850349528589023760741)
    ·
      refine ⟨128784440536610441955139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 686850349528589023760741 128784440536610441955139)
      ·
        refine ⟨193176660804915662932709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128784440536610441955139 193176660804915662932709)
        ·
          refine ⟨36220623900921686799883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193176660804915662932709 36220623900921686799883)
          ·
            refine ⟨54330935851382530199825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36220623900921686799883 54330935851382530199825)
            ·
              refine ⟨40748201888536897649869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54330935851382530199825 40748201888536897649869)
              ·
                refine ⟨15280575708201336618701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40748201888536897649869 15280575708201336618701)
                ·
                  rfl

theorem cell19_50218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_50218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50218 prefixEnd_50218 := by exact prefixLift 50218
  have htrace : WordTrace (prefixWord ++ tailWord_50218) baseStart_50218 baseEnd_50218 := by
    simpa [prefixWord, tailWord_50218, baseEnd_50218] using wordTrace_append hprefix tailTrace_50218
  have hstable : (prefixWord ++ tailWord_50218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50218).length < 2 ^ (prefixWord ++ tailWord_50218).sum := by decide
  have hdescent : baseEnd_50218 < baseStart_50218 := by decide
  rcases family_descends (prefixWord ++ tailWord_50218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50241 : List Nat := [1, 2, 5, 1, 3, 2, 5]
def baseStart_50241 : Nat := 118140960795 + 50241 * 2 ^ 59
def prefixEnd_50241 : Nat := 4983230072969 + 3 ^ 40 * 50241 * 2
def baseEnd_50241 : Nat := 5095858086448032702509

theorem tailTrace_50241 : CollatzResearch.WordTrace tailWord_50241 prefixEnd_50241 5095858086448032702509 := by
  unfold tailWord_50241
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832439810992912324782577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1221626540661941549855051 1832439810992912324782577)
  ·
    refine ⟨1374329858244684243586933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1832439810992912324782577 1374329858244684243586933)
    ·
      refine ⟨128843424210439147836275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1374329858244684243586933 128843424210439147836275)
      ·
        refine ⟨193265136315658721754413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128843424210439147836275 193265136315658721754413)
        ·
          refine ⟨72474426118372020657905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193265136315658721754413 72474426118372020657905)
          ·
            refine ⟨54355819588779015493429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72474426118372020657905 54355819588779015493429)
            ·
              refine ⟨5095858086448032702509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54355819588779015493429 5095858086448032702509)
              ·
                rfl

theorem cell19_50241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_50241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50241 prefixEnd_50241 := by exact prefixLift 50241
  have htrace : WordTrace (prefixWord ++ tailWord_50241) baseStart_50241 baseEnd_50241 := by
    simpa [prefixWord, tailWord_50241, baseEnd_50241] using wordTrace_append hprefix tailTrace_50241
  have hstable : (prefixWord ++ tailWord_50241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50241).length < 2 ^ (prefixWord ++ tailWord_50241).sum := by decide
  have hdescent : baseEnd_50241 < baseStart_50241 := by decide
  rcases family_descends (prefixWord ++ tailWord_50241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50245 : List Nat := [1, 3, 1, 1, 1, 3, 9]
def baseStart_50245 : Nat := 118140960795 + 50245 * 2 ^ 59
def prefixEnd_50245 : Nat := 4983230072969 + 3 ^ 40 * 50245 * 2
def baseEnd_50245 : Nat := 5096263799557758006209

theorem tailTrace_50245 : CollatzResearch.WordTrace tailWord_50245 prefixEnd_50245 5096263799557758006209 := by
  unfold tailWord_50245
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832585702978421007928189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1221723801985614005285459 1832585702978421007928189)
  ·
    refine ⟨687219638616907877973071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1832585702978421007928189 687219638616907877973071)
    ·
      refine ⟨1030829457925361816959607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687219638616907877973071 1030829457925361816959607)
      ·
        refine ⟨1546244186888042725439411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030829457925361816959607 1546244186888042725439411)
        ·
          refine ⟨2319366280332064088159117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546244186888042725439411 2319366280332064088159117)
          ·
            refine ⟨869762355124524033059669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2319366280332064088159117 869762355124524033059669)
            ·
              refine ⟨5096263799557758006209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 869762355124524033059669 5096263799557758006209)
              ·
                rfl

theorem cell19_50245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_50245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50245 prefixEnd_50245 := by exact prefixLift 50245
  have htrace : WordTrace (prefixWord ++ tailWord_50245) baseStart_50245 baseEnd_50245 := by
    simpa [prefixWord, tailWord_50245, baseEnd_50245] using wordTrace_append hprefix tailTrace_50245
  have hstable : (prefixWord ++ tailWord_50245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50245).length < 2 ^ (prefixWord ++ tailWord_50245).sum := by decide
  have hdescent : baseEnd_50245 < baseStart_50245 := by decide
  rcases family_descends (prefixWord ++ tailWord_50245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50334 : List Nat := [4, 3, 1, 1, 2, 2, 3, 3]
def baseStart_50334 : Nat := 118140960795 + 50334 * 2 ^ 59
def prefixEnd_50334 : Nat := 4983230072969 + 3 ^ 40 * 50334 * 2
def baseEnd_50334 : Nat := 15315872748747438040607

theorem tailTrace_50334 : CollatzResearch.WordTrace tailWord_50334 prefixEnd_50334 15315872748747438040607 := by
  unfold tailWord_50334
  simp only [CollatzResearch.WordTrace]
  refine ⟨229478974956998650989757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1223887866437326138612037 229478974956998650989757)
  ·
    refine ⟨86054615608874494121159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229478974956998650989757 86054615608874494121159)
    ·
      refine ⟨129081923413311741181739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86054615608874494121159 129081923413311741181739)
      ·
        refine ⟨193622885119967611772609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129081923413311741181739 193622885119967611772609)
        ·
          refine ⟨145217163839975708829457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193622885119967611772609 145217163839975708829457)
          ·
            refine ⟨108912872879981781622093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145217163839975708829457 108912872879981781622093)
            ·
              refine ⟨40842327329993168108285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108912872879981781622093 40842327329993168108285)
              ·
                refine ⟨15315872748747438040607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40842327329993168108285 15315872748747438040607)
                ·
                  rfl

theorem cell19_50334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_50334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50334 prefixEnd_50334 := by exact prefixLift 50334
  have htrace : WordTrace (prefixWord ++ tailWord_50334) baseStart_50334 baseEnd_50334 := by
    simpa [prefixWord, tailWord_50334, baseEnd_50334] using wordTrace_append hprefix tailTrace_50334
  have hstable : (prefixWord ++ tailWord_50334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50334).length < 2 ^ (prefixWord ++ tailWord_50334).sum := by decide
  have hdescent : baseEnd_50334 < baseStart_50334 := by decide
  rcases family_descends (prefixWord ++ tailWord_50334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50359 : List Nat := [1, 1, 3, 1, 4, 1, 8]
def baseStart_50359 : Nat := 118140960795 + 50359 * 2 ^ 59
def prefixEnd_50359 : Nat := 4983230072969 + 3 ^ 40 * 50359 * 2
def baseEnd_50359 : Nat := 5107826623184929161661

theorem tailTrace_50359 : CollatzResearch.WordTrace tailWord_50359 prefixEnd_50359 5107826623184929161661 := by
  unfold tailWord_50359
  simp only [CollatzResearch.WordTrace]
  refine ⟨1836743624565418477578131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1224495749710278985052087 1836743624565418477578131)
  ·
    refine ⟨2755115436848127716367197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1836743624565418477578131 2755115436848127716367197)
    ·
      refine ⟨1033168288818047893637699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2755115436848127716367197 1033168288818047893637699)
      ·
        refine ⟨1549752433227071840456549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033168288818047893637699 1549752433227071840456549)
        ·
          refine ⟨290578581230075970085603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1549752433227071840456549 290578581230075970085603)
          ·
            refine ⟨435867871845113955128405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290578581230075970085603 435867871845113955128405)
            ·
              refine ⟨5107826623184929161661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 435867871845113955128405 5107826623184929161661)
              ·
                rfl

theorem cell19_50359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_50359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50359 prefixEnd_50359 := by exact prefixLift 50359
  have htrace : WordTrace (prefixWord ++ tailWord_50359) baseStart_50359 baseEnd_50359 := by
    simpa [prefixWord, tailWord_50359, baseEnd_50359] using wordTrace_append hprefix tailTrace_50359
  have hstable : (prefixWord ++ tailWord_50359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50359).length < 2 ^ (prefixWord ++ tailWord_50359).sum := by decide
  have hdescent : baseEnd_50359 < baseStart_50359 := by decide
  rcases family_descends (prefixWord ++ tailWord_50359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50433 : List Nat := [1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_50433 : Nat := 118140960795 + 50433 * 2 ^ 59
def prefixEnd_50433 : Nat := 4983230072969 + 3 ^ 40 * 50433 * 2
def baseEnd_50433 : Nat := 15345996947144541840337

theorem tailTrace_50433 : CollatzResearch.WordTrace tailWord_50433 prefixEnd_50433 15345996947144541840337 := by
  unfold tailWord_50433
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839442626297329115771953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1226295084198219410514635 1839442626297329115771953)
  ·
    refine ⟨1379581969722996836828965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1839442626297329115771953 1379581969722996836828965)
    ·
      refine ⟨258671619323061906905431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1379581969722996836828965 258671619323061906905431)
      ·
        refine ⟨388007428984592860358147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258671619323061906905431 388007428984592860358147)
        ·
          refine ⟨582011143476889290537221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388007428984592860358147 582011143476889290537221)
          ·
            refine ⟨109127089401916741975729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 582011143476889290537221 109127089401916741975729)
            ·
              refine ⟨81845317051437556481797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109127089401916741975729 81845317051437556481797)
              ·
                refine ⟨15345996947144541840337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81845317051437556481797 15345996947144541840337)
                ·
                  rfl

theorem cell19_50433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_50433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50433 prefixEnd_50433 := by exact prefixLift 50433
  have htrace : WordTrace (prefixWord ++ tailWord_50433) baseStart_50433 baseEnd_50433 := by
    simpa [prefixWord, tailWord_50433, baseEnd_50433] using wordTrace_append hprefix tailTrace_50433
  have hstable : (prefixWord ++ tailWord_50433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50433).length < 2 ^ (prefixWord ++ tailWord_50433).sum := by decide
  have hdescent : baseEnd_50433 < baseStart_50433 := by decide
  rcases family_descends (prefixWord ++ tailWord_50433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50435 : List Nat := [1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_50435 : Nat := 118140960795 + 50435 * 2 ^ 59
def prefixEnd_50435 : Nat := 4983230072969 + 3 ^ 40 * 50435 * 2
def baseEnd_50435 : Nat := 15346605516809129795887

theorem tailTrace_50435 : CollatzResearch.WordTrace tailWord_50435 prefixEnd_50435 15346605516809129795887 := by
  unfold tailWord_50435
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839515572290083457344759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1226343714860055638229839 1839515572290083457344759)
  ·
    refine ⟨2759273358435125186017139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1839515572290083457344759 2759273358435125186017139)
    ·
      refine ⟨4138910037652687779025709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759273358435125186017139 4138910037652687779025709)
      ·
        refine ⟨1552091264119757917134641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4138910037652687779025709 1552091264119757917134641)
        ·
          refine ⟨1164068448089818437850981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552091264119757917134641 1164068448089818437850981)
          ·
            refine ⟨218262834016840957097059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1164068448089818437850981 218262834016840957097059)
            ·
              refine ⟨327394251025261435645589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218262834016840957097059 327394251025261435645589)
              ·
                refine ⟨15346605516809129795887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 327394251025261435645589 15346605516809129795887)
                ·
                  rfl

theorem cell19_50435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_50435 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50435 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50435 prefixEnd_50435 := by exact prefixLift 50435
  have htrace : WordTrace (prefixWord ++ tailWord_50435) baseStart_50435 baseEnd_50435 := by
    simpa [prefixWord, tailWord_50435, baseEnd_50435] using wordTrace_append hprefix tailTrace_50435
  have hstable : (prefixWord ++ tailWord_50435).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50435).length < 2 ^ (prefixWord ++ tailWord_50435).sum := by decide
  have hdescent : baseEnd_50435 < baseStart_50435 := by decide
  rcases family_descends (prefixWord ++ tailWord_50435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50471 : List Nat := [1, 1, 8, 9]
def baseStart_50471 : Nat := 118140960795 + 50471 * 2 ^ 59
def prefixEnd_50471 : Nat := 4983230072969 + 3 ^ 40 * 50471 * 2
def baseEnd_50471 : Nat := 189599503342860654269

theorem tailTrace_50471 : CollatzResearch.WordTrace tailWord_50471 prefixEnd_50471 189599503342860654269 := by
  unfold tailWord_50471
  simp only [CollatzResearch.WordTrace]
  refine ⟨1840828600159661605655267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1227219066773107737103511 1840828600159661605655267)
  ·
    refine ⟨2761242900239492408482901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1840828600159661605655267 2761242900239492408482901)
    ·
      refine ⟨32358315237181551661909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 2761242900239492408482901 32358315237181551661909)
      ·
        refine ⟨189599503342860654269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 32358315237181551661909 189599503342860654269)
        ·
          rfl

theorem cell19_50471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 9].length) (baseStart_50471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50471 prefixEnd_50471 := by exact prefixLift 50471
  have htrace : WordTrace (prefixWord ++ tailWord_50471) baseStart_50471 baseEnd_50471 := by
    simpa [prefixWord, tailWord_50471, baseEnd_50471] using wordTrace_append hprefix tailTrace_50471
  have hstable : (prefixWord ++ tailWord_50471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50471).length < 2 ^ (prefixWord ++ tailWord_50471).sum := by decide
  have hdescent : baseEnd_50471 < baseStart_50471 := by decide
  rcases family_descends (prefixWord ++ tailWord_50471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50558 : List Nat := [4, 2, 3, 2, 2, 1, 2, 3]
def baseStart_50558 : Nat := 118140960795 + 50558 * 2 ^ 59
def prefixEnd_50558 : Nat := 4983230072969 + 3 ^ 40 * 50558 * 2
def baseEnd_50558 : Nat := 15384032551181289062219

theorem tailTrace_50558 : CollatzResearch.WordTrace tailWord_50558 prefixEnd_50558 15384032551181289062219 := by
  unfold tailWord_50558
  simp only [CollatzResearch.WordTrace]
  refine ⟨230500218855559433009041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1229334500562983642714885 230500218855559433009041)
  ·
    refine ⟨172875164141669574756781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230500218855559433009041 172875164141669574756781)
    ·
      refine ⟨64828186553126090533793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172875164141669574756781 64828186553126090533793)
      ·
        refine ⟨48621139914844567900345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64828186553126090533793 48621139914844567900345)
        ·
          refine ⟨36465854936133425925259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48621139914844567900345 36465854936133425925259)
          ·
            refine ⟨54698782404200138887889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36465854936133425925259 54698782404200138887889)
            ·
              refine ⟨41024086803150104165917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54698782404200138887889 41024086803150104165917)
              ·
                refine ⟨15384032551181289062219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41024086803150104165917 15384032551181289062219)
                ·
                  rfl

theorem cell19_50558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_50558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50558 prefixEnd_50558 := by exact prefixLift 50558
  have htrace : WordTrace (prefixWord ++ tailWord_50558) baseStart_50558 baseEnd_50558 := by
    simpa [prefixWord, tailWord_50558, baseEnd_50558] using wordTrace_append hprefix tailTrace_50558
  have hstable : (prefixWord ++ tailWord_50558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50558).length < 2 ^ (prefixWord ++ tailWord_50558).sum := by decide
  have hdescent : baseEnd_50558 < baseStart_50558 := by decide
  rcases family_descends (prefixWord ++ tailWord_50558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
