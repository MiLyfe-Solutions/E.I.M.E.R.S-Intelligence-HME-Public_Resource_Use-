import V185TrunkScan23Chunk0686

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4062240 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4062240 : Nat := 118140960795 + 4062240 * 2 ^ 59
def prefixEnd_4062240 : Nat := 4983230072969 + 3 ^ 40 * 4062240 * 2
def baseEnd_4062240 : Nat := 2085881653920291701018105

theorem tailTrace_4062240 : CollatzResearch.WordTrace tailWord_4062240 prefixEnd_4062240 2085881653920291701018105 := by
  unfold tailWord_4062240
  simp only [CollatzResearch.WordTrace]
  refine ⟨74081032401602865101416087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98774709868803820135221449 74081032401602865101416087)
  ·
    refine ⟨111121548602404297652124131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74081032401602865101416087 111121548602404297652124131)
    ·
      refine ⟨166682322903606446478186197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111121548602404297652124131 166682322903606446478186197)
      ·
        refine ⟨3906616943053276089332489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 166682322903606446478186197 3906616943053276089332489)
        ·
          refine ⟨2929962707289957066999367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3906616943053276089332489 2929962707289957066999367)
          ·
            refine ⟨4394944060934935600499051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929962707289957066999367 4394944060934935600499051)
            ·
              refine ⟨6592416091402403400748577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4394944060934935600499051 6592416091402403400748577)
              ·
                refine ⟨4944312068551802550561433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6592416091402403400748577 4944312068551802550561433)
                ·
                  refine ⟨3708234051413851912921075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4944312068551802550561433 3708234051413851912921075)
                  ·
                    refine ⟨5562351077120777869381613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3708234051413851912921075 5562351077120777869381613)
                    ·
                      refine ⟨2085881653920291701018105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5562351077120777869381613 2085881653920291701018105)
                      ·
                        rfl

theorem cell23_4062240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4062240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062240 prefixEnd_4062240 := by exact prefixLift 4062240
  have htrace : WordTrace (prefixWord ++ tailWord_4062240) baseStart_4062240 baseEnd_4062240 := by
    simpa [prefixWord, tailWord_4062240, baseEnd_4062240] using wordTrace_append hprefix tailTrace_4062240
  have hstable : (prefixWord ++ tailWord_4062240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062240).length < 2 ^ (prefixWord ++ tailWord_4062240).sum := by decide
  have hdescent : baseEnd_4062240 < baseStart_4062240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062242 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_4062242 : Nat := 118140960795 + 4062242 * 2 ^ 59
def prefixEnd_4062242 : Nat := 4983230072969 + 3 ^ 40 * 4062242 * 2
def baseEnd_4062242 : Nat := 2085882680881600693193095

theorem tailTrace_4062242 : CollatzResearch.WordTrace tailWord_4062242 prefixEnd_4062242 2085882680881600693193095 := by
  unfold tailWord_4062242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37040534437299621136101245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98774758499465656362936653 37040534437299621136101245)
  ·
    refine ⟨13890200413987357926037967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37040534437299621136101245 13890200413987357926037967)
    ·
      refine ⟨20835300620981036889056951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13890200413987357926037967 20835300620981036889056951)
      ·
        refine ⟨31252950931471555333585427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20835300620981036889056951 31252950931471555333585427)
        ·
          refine ⟨46879426397207333000378141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31252950931471555333585427 46879426397207333000378141)
          ·
            refine ⟨17579784898952749875141803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46879426397207333000378141 17579784898952749875141803)
            ·
              refine ⟨26369677348429124812712705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17579784898952749875141803 26369677348429124812712705)
              ·
                refine ⟨19777258011321843609534529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26369677348429124812712705 19777258011321843609534529)
                ·
                  refine ⟨14832943508491382707150897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19777258011321843609534529 14832943508491382707150897)
                  ·
                    refine ⟨11124707631368537030363173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14832943508491382707150897 11124707631368537030363173)
                    ·
                      refine ⟨2085882680881600693193095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11124707631368537030363173 2085882680881600693193095)
                      ·
                        rfl

theorem cell23_4062242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_4062242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062242 prefixEnd_4062242 := by exact prefixLift 4062242
  have htrace : WordTrace (prefixWord ++ tailWord_4062242) baseStart_4062242 baseEnd_4062242 := by
    simpa [prefixWord, tailWord_4062242, baseEnd_4062242] using wordTrace_append hprefix tailTrace_4062242
  have hstable : (prefixWord ++ tailWord_4062242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062242).length < 2 ^ (prefixWord ++ tailWord_4062242).sum := by decide
  have hdescent : baseEnd_4062242 < baseStart_4062242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062252 : List Nat := [2, 2, 1, 1, 1, 2, 3, 6, 5]
def baseStart_4062252 : Nat := 118140960795 + 4062252 * 2 ^ 59
def prefixEnd_4062252 : Nat := 4983230072969 + 3 ^ 40 * 4062252 * 2
def baseEnd_4062252 : Nat := 231765312854238406007561

theorem tailTrace_4062252 : CollatzResearch.WordTrace tailWord_4062252 prefixEnd_4062252 231765312854238406007561 := by
  unfold tailWord_4062252
  simp only [CollatzResearch.WordTrace]
  refine ⟨74081251239581128126134505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98775001652774837501512673 74081251239581128126134505)
  ·
    refine ⟨55560938429685846094600879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74081251239581128126134505 55560938429685846094600879)
    ·
      refine ⟨83341407644528769141901319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55560938429685846094600879 83341407644528769141901319)
      ·
        refine ⟨125012111466793153712851979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83341407644528769141901319 125012111466793153712851979)
        ·
          refine ⟨187518167200189730569277969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125012111466793153712851979 187518167200189730569277969)
          ·
            refine ⟨140638625400142297926958477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187518167200189730569277969 140638625400142297926958477)
            ·
              refine ⟨52739484525053361722609429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140638625400142297926958477 52739484525053361722609429)
              ·
                refine ⟨2472163337111876330747317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52739484525053361722609429 2472163337111876330747317)
                ·
                  refine ⟨231765312854238406007561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2472163337111876330747317 231765312854238406007561)
                  ·
                    rfl

theorem cell23_4062252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_4062252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062252 prefixEnd_4062252 := by exact prefixLift 4062252
  have htrace : WordTrace (prefixWord ++ tailWord_4062252) baseStart_4062252 baseEnd_4062252 := by
    simpa [prefixWord, tailWord_4062252, baseEnd_4062252] using wordTrace_append hprefix tailTrace_4062252
  have hstable : (prefixWord ++ tailWord_4062252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062252).length < 2 ^ (prefixWord ++ tailWord_4062252).sum := by decide
  have hdescent : baseEnd_4062252 < baseStart_4062252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062339 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 3]
def baseStart_4062339 : Nat := 118140960795 + 4062339 * 2 ^ 59
def prefixEnd_4062339 : Nat := 4983230072969 + 3 ^ 40 * 4062339 * 2
def baseEnd_4062339 : Nat := 2085932488505086813680149

theorem tailTrace_4062339 : CollatzResearch.WordTrace tailWord_4062339 prefixEnd_4062339 2085932488505086813680149 := by
  unfold tailWord_4062339
  simp only [CollatzResearch.WordTrace]
  refine ⟨148165675629847070110686071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98777117086564713407124047 148165675629847070110686071)
  ·
    refine ⟨222248513444770605166029107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148165675629847070110686071 222248513444770605166029107)
    ·
      refine ⟨333372770167155907749043661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222248513444770605166029107 333372770167155907749043661)
      ·
        refine ⟨125014788812683465405891373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333372770167155907749043661 125014788812683465405891373)
        ·
          refine ⟨46880545804756299527209265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125014788812683465405891373 46880545804756299527209265)
          ·
            refine ⟨35160409353567224645406949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46880545804756299527209265 35160409353567224645406949)
            ·
              refine ⟨6592576753793854621013803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35160409353567224645406949 6592576753793854621013803)
              ·
                refine ⟨9888865130690781931520705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592576753793854621013803 9888865130690781931520705)
                ·
                  refine ⟨7416648848018086448640529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9888865130690781931520705 7416648848018086448640529)
                  ·
                    refine ⟨5562486636013564836480397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7416648848018086448640529 5562486636013564836480397)
                    ·
                      refine ⟨2085932488505086813680149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5562486636013564836480397 2085932488505086813680149)
                      ·
                        rfl

theorem cell23_4062339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_4062339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062339 prefixEnd_4062339 := by exact prefixLift 4062339
  have htrace : WordTrace (prefixWord ++ tailWord_4062339) baseStart_4062339 baseEnd_4062339 := by
    simpa [prefixWord, tailWord_4062339, baseEnd_4062339] using wordTrace_append hprefix tailTrace_4062339
  have hstable : (prefixWord ++ tailWord_4062339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062339).length < 2 ^ (prefixWord ++ tailWord_4062339).sum := by decide
  have hdescent : baseEnd_4062339 < baseStart_4062339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062346 : List Nat := [3, 1, 2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_4062346 : Nat := 118140960795 + 4062346 * 2 ^ 59
def prefixEnd_4062346 : Nat := 4983230072969 + 3 ^ 40 * 4062346 * 2
def baseEnd_4062346 : Nat := 695312027623222762097539

theorem tailTrace_4062346 : CollatzResearch.WordTrace tailWord_4062346 prefixEnd_4062346 695312027623222762097539 := by
  unfold tailWord_4062346
  simp only [CollatzResearch.WordTrace]
  refine ⟨37041482735205427576547723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98777287293881140204127261 37041482735205427576547723)
  ·
    refine ⟨55562224102808141364821585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37041482735205427576547723 55562224102808141364821585)
    ·
      refine ⟨41671668077106106023616189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55562224102808141364821585 41671668077106106023616189)
      ·
        refine ⟨15626875528914789758856071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41671668077106106023616189 15626875528914789758856071)
        ·
          refine ⟨23440313293372184638284107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15626875528914789758856071 23440313293372184638284107)
          ·
            refine ⟨35160469940058276957426161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23440313293372184638284107 35160469940058276957426161)
            ·
              refine ⟨26370352455043707718069621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35160469940058276957426161 26370352455043707718069621)
              ·
                refine ⟨2472220542660347598569027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26370352455043707718069621 2472220542660347598569027)
                ·
                  refine ⟨3708330813990521397853541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472220542660347598569027 3708330813990521397853541)
                  ·
                    refine ⟨695312027623222762097539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708330813990521397853541 695312027623222762097539)
                    ·
                      rfl

theorem cell23_4062346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_4062346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062346 prefixEnd_4062346 := by exact prefixLift 4062346
  have htrace : WordTrace (prefixWord ++ tailWord_4062346) baseStart_4062346 baseEnd_4062346 := by
    simpa [prefixWord, tailWord_4062346, baseEnd_4062346] using wordTrace_append hprefix tailTrace_4062346
  have hstable : (prefixWord ++ tailWord_4062346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062346).length < 2 ^ (prefixWord ++ tailWord_4062346).sum := by decide
  have hdescent : baseEnd_4062346 < baseStart_4062346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062359 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 6]
def baseStart_4062359 : Nat := 118140960795 + 4062359 * 2 ^ 59
def prefixEnd_4062359 : Nat := 4983230072969 + 3 ^ 40 * 4062359 * 2
def baseEnd_4062359 : Nat := 231771417568686303936673

theorem tailTrace_4062359 : CollatzResearch.WordTrace tailWord_4062359 prefixEnd_4062359 231771417568686303936673 := by
  unfold tailWord_4062359
  simp only [CollatzResearch.WordTrace]
  refine ⟨148166405089774613526414131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98777603393183075684276087 148166405089774613526414131)
  ·
    refine ⟨222249607634661920289621197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148166405089774613526414131 222249607634661920289621197)
    ·
      refine ⟨83343602862998220108607949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222249607634661920289621197 83343602862998220108607949)
      ·
        refine ⟨31253851073624332540727981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83343602862998220108607949 31253851073624332540727981)
        ·
          refine ⟨11720194152609124702772993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31253851073624332540727981 11720194152609124702772993)
          ·
            refine ⟨8790145614456843527079745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11720194152609124702772993 8790145614456843527079745)
            ·
              refine ⟨6592609210842632645309809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8790145614456843527079745 6592609210842632645309809)
              ·
                refine ⟨4944456908131974483982357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6592609210842632645309809 4944456908131974483982357)
                ·
                  refine ⟨231771417568686303936673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4944456908131974483982357 231771417568686303936673)
                  ·
                    rfl

theorem cell23_4062359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 6].length) (baseStart_4062359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062359 prefixEnd_4062359 := by exact prefixLift 4062359
  have htrace : WordTrace (prefixWord ++ tailWord_4062359) baseStart_4062359 baseEnd_4062359 := by
    simpa [prefixWord, tailWord_4062359, baseEnd_4062359] using wordTrace_append hprefix tailTrace_4062359
  have hstable : (prefixWord ++ tailWord_4062359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062359).length < 2 ^ (prefixWord ++ tailWord_4062359).sum := by decide
  have hdescent : baseEnd_4062359 < baseStart_4062359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062386 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_4062386 : Nat := 118140960795 + 4062386 * 2 ^ 59
def prefixEnd_4062386 : Nat := 4983230072969 + 3 ^ 40 * 4062386 * 2
def baseEnd_4062386 : Nat := 2085956622095848129792433

theorem tailTrace_4062386 : CollatzResearch.WordTrace tailWord_4062386 prefixEnd_4062386 2085956622095848129792433 := by
  unfold tailWord_4062386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37041847465169199284411753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98778259907117864758431341 37041847465169199284411753)
  ·
    refine ⟨27781385598876899463308815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37041847465169199284411753 27781385598876899463308815)
    ·
      refine ⟨41672078398315349194963223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27781385598876899463308815 41672078398315349194963223)
      ·
        refine ⟨62508117597473023792444835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41672078398315349194963223 62508117597473023792444835)
        ·
          refine ⟨93762176396209535688667253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62508117597473023792444835 93762176396209535688667253)
          ·
            refine ⟨8790204037144643970812555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93762176396209535688667253 8790204037144643970812555)
            ·
              refine ⟨13185306055716965956218833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790204037144643970812555 13185306055716965956218833)
              ·
                refine ⟨9888979541787724467164125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13185306055716965956218833 9888979541787724467164125)
                ·
                  refine ⟨3708367328170396675186547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9888979541787724467164125 3708367328170396675186547)
                  ·
                    refine ⟨5562550992255595012779821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3708367328170396675186547 5562550992255595012779821)
                    ·
                      refine ⟨2085956622095848129792433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5562550992255595012779821 2085956622095848129792433)
                      ·
                        rfl

theorem cell23_4062386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_4062386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062386 prefixEnd_4062386 := by exact prefixLift 4062386
  have htrace : WordTrace (prefixWord ++ tailWord_4062386) baseStart_4062386 baseEnd_4062386 := by
    simpa [prefixWord, tailWord_4062386, baseEnd_4062386] using wordTrace_append hprefix tailTrace_4062386
  have hstable : (prefixWord ++ tailWord_4062386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062386).length < 2 ^ (prefixWord ++ tailWord_4062386).sum := by decide
  have hdescent : baseEnd_4062386 < baseStart_4062386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062396 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_4062396 : Nat := 118140960795 + 4062396 * 2 ^ 59
def prefixEnd_4062396 : Nat := 4983230072969 + 3 ^ 40 * 4062396 * 2
def baseEnd_4062396 : Nat := 2085961756902393090667387

theorem tailTrace_4062396 : CollatzResearch.WordTrace tailWord_4062396 prefixEnd_4062396 2085961756902393090667387 := by
  unfold tailWord_4062396
  simp only [CollatzResearch.WordTrace]
  refine ⟨74083877295320284422755521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98778503060427045897007361 74083877295320284422755521)
  ·
    refine ⟨55562907971490213317066641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74083877295320284422755521 55562907971490213317066641)
    ·
      refine ⟨41672180978617659987799981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55562907971490213317066641 41672180978617659987799981)
      ·
        refine ⟨15627067866981622495424993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41672180978617659987799981 15627067866981622495424993)
        ·
          refine ⟨11720300900236216871568745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15627067866981622495424993 11720300900236216871568745)
          ·
            refine ⟨8790225675177162653676559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11720300900236216871568745 8790225675177162653676559)
            ·
              refine ⟨13185338512765743980514839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790225675177162653676559 13185338512765743980514839)
              ·
                refine ⟨19778007769148615970772259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13185338512765743980514839 19778007769148615970772259)
                ·
                  refine ⟨29667011653722923956158389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19778007769148615970772259 29667011653722923956158389)
                  ·
                    refine ⟨2781282342536524120889849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29667011653722923956158389 2781282342536524120889849)
                    ·
                      refine ⟨2085961756902393090667387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781282342536524120889849 2085961756902393090667387)
                      ·
                        rfl

theorem cell23_4062396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_4062396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062396 prefixEnd_4062396 := by exact prefixLift 4062396
  have htrace : WordTrace (prefixWord ++ tailWord_4062396) baseStart_4062396 baseEnd_4062396 := by
    simpa [prefixWord, tailWord_4062396, baseEnd_4062396] using wordTrace_append hprefix tailTrace_4062396
  have hstable : (prefixWord ++ tailWord_4062396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062396).length < 2 ^ (prefixWord ++ tailWord_4062396).sum := by decide
  have hdescent : baseEnd_4062396 < baseStart_4062396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062420 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4062420 : Nat := 118140960795 + 4062420 * 2 ^ 59
def prefixEnd_4062420 : Nat := 4983230072969 + 3 ^ 40 * 4062420 * 2
def baseEnd_4062420 : Nat := 2085974080438100996767277

theorem tailTrace_4062420 : CollatzResearch.WordTrace tailWord_4062420 prefixEnd_4062420 2085974080438100996767277 := by
  unfold tailWord_4062420
  simp only [CollatzResearch.WordTrace]
  refine ⟨74084314971276810472192357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98779086628369080629589809 74084314971276810472192357)
  ·
    refine ⟨13890809057114401963536067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74084314971276810472192357 13890809057114401963536067)
    ·
      refine ⟨20836213585671602945304101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13890809057114401963536067 20836213585671602945304101)
      ·
        refine ⟨3906790047313425552244519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20836213585671602945304101 3906790047313425552244519)
        ·
          refine ⟨5860185070970138328366779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906790047313425552244519 5860185070970138328366779)
          ·
            refine ⟨8790277606455207492550169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860185070970138328366779 8790277606455207492550169)
            ·
              refine ⟨6592708204841405619412627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8790277606455207492550169 6592708204841405619412627)
              ·
                refine ⟨9889062307262108429118941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592708204841405619412627 9889062307262108429118941)
                ·
                  refine ⟨3708398365223290660919603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9889062307262108429118941 3708398365223290660919603)
                  ·
                    refine ⟨5562597547834935991379405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3708398365223290660919603 5562597547834935991379405)
                    ·
                      refine ⟨2085974080438100996767277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5562597547834935991379405 2085974080438100996767277)
                      ·
                        rfl

theorem cell23_4062420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4062420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062420 prefixEnd_4062420 := by exact prefixLift 4062420
  have htrace : WordTrace (prefixWord ++ tailWord_4062420) baseStart_4062420 baseEnd_4062420 := by
    simpa [prefixWord, tailWord_4062420, baseEnd_4062420] using wordTrace_append hprefix tailTrace_4062420
  have hstable : (prefixWord ++ tailWord_4062420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062420).length < 2 ^ (prefixWord ++ tailWord_4062420).sum := by decide
  have hdescent : baseEnd_4062420 < baseStart_4062420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062446 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_4062446 : Nat := 118140960795 + 4062446 * 2 ^ 59
def prefixEnd_4062446 : Nat := 4983230072969 + 3 ^ 40 * 4062446 * 2
def baseEnd_4062446 : Nat := 2085987430935117895042157

theorem tailTrace_4062446 : CollatzResearch.WordTrace tailWord_4062446 prefixEnd_4062446 2085987430935117895042157 := by
  unfold tailWord_4062446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18521197280057428423103899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98779718826972951589887461 18521197280057428423103899)
  ·
    refine ⟨27781795920086142634655849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18521197280057428423103899 27781795920086142634655849)
    ·
      refine ⟨20836346940064606975991887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27781795920086142634655849 20836346940064606975991887)
      ·
        refine ⟨31254520410096910463987831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20836346940064606975991887 31254520410096910463987831)
        ·
          refine ⟨46881780615145365695981747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31254520410096910463987831 46881780615145365695981747)
          ·
            refine ⟨70322670922718048543972621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46881780615145365695981747 70322670922718048543972621)
            ·
              refine ⟨26371001596019268203989733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70322670922718048543972621 26371001596019268203989733)
              ·
                refine ⟨4944562799253612788248075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26371001596019268203989733 4944562799253612788248075)
                ·
                  refine ⟨7416844198880419182372113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944562799253612788248075 7416844198880419182372113)
                  ·
                    refine ⟨5562633149160314386779085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7416844198880419182372113 5562633149160314386779085)
                    ·
                      refine ⟨2085987430935117895042157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5562633149160314386779085 2085987430935117895042157)
                      ·
                        rfl

theorem cell23_4062446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_4062446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062446 prefixEnd_4062446 := by exact prefixLift 4062446
  have htrace : WordTrace (prefixWord ++ tailWord_4062446) baseStart_4062446 baseEnd_4062446 := by
    simpa [prefixWord, tailWord_4062446, baseEnd_4062446] using wordTrace_append hprefix tailTrace_4062446
  have hstable : (prefixWord ++ tailWord_4062446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062446).length < 2 ^ (prefixWord ++ tailWord_4062446).sum := by decide
  have hdescent : baseEnd_4062446 < baseStart_4062446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062466 : List Nat := [3, 4, 1, 1, 3, 2, 9]
def baseStart_4062466 : Nat := 118140960795 + 4062466 * 2 ^ 59
def prefixEnd_4062466 : Nat := 4983230072969 + 3 ^ 40 * 4062466 * 2
def baseEnd_4062466 : Nat := 25753058031459355762865

theorem tailTrace_4062466 : CollatzResearch.WordTrace tailWord_4062466 prefixEnd_4062466 25753058031459355762865 := by
  unfold tailWord_4062466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37042576925096742700139813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98780205133591313867039501 37042576925096742700139813)
  ·
    refine ⟨6945483173455639256276215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37042576925096742700139813 6945483173455639256276215)
    ·
      refine ⟨10418224760183458884414323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6945483173455639256276215 10418224760183458884414323)
      ·
        refine ⟨15627337140275188326621485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10418224760183458884414323 15627337140275188326621485)
        ·
          refine ⟨5860251427603195622483057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15627337140275188326621485 5860251427603195622483057)
          ·
            refine ⟨4395188570702396716862293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5860251427603195622483057 4395188570702396716862293)
            ·
              refine ⟨25753058031459355762865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4395188570702396716862293 25753058031459355762865)
              ·
                rfl

theorem cell23_4062466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 9].length) (baseStart_4062466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062466 prefixEnd_4062466 := by exact prefixLift 4062466
  have htrace : WordTrace (prefixWord ++ tailWord_4062466) baseStart_4062466 baseEnd_4062466 := by
    simpa [prefixWord, tailWord_4062466, baseEnd_4062466] using wordTrace_append hprefix tailTrace_4062466
  have hstable : (prefixWord ++ tailWord_4062466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062466).length < 2 ^ (prefixWord ++ tailWord_4062466).sum := by decide
  have hdescent : baseEnd_4062466 < baseStart_4062466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062476 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 4, 1, 3]
def baseStart_4062476 : Nat := 118140960795 + 4062476 * 2 ^ 59
def prefixEnd_4062476 : Nat := 4983230072969 + 3 ^ 40 * 4062476 * 2
def baseEnd_4062476 : Nat := 2086002835354752777667019

theorem tailTrace_4062476 : CollatzResearch.WordTrace tailWord_4062476 prefixEnd_4062476 2086002835354752777667019 := by
  unfold tailWord_4062476
  simp only [CollatzResearch.WordTrace]
  refine ⟨74085336215175371254211641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98780448286900495005615521 74085336215175371254211641)
  ·
    refine ⟨55564002161381528440658731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74085336215175371254211641 55564002161381528440658731)
    ·
      refine ⟨83346003242072292660988097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55564002161381528440658731 83346003242072292660988097)
      ·
        refine ⟨62509502431554219495741073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83346003242072292660988097 62509502431554219495741073)
        ·
          refine ⟨46882126823665664621805805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62509502431554219495741073 46882126823665664621805805)
          ·
            refine ⟨17580797558874624233177177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46882126823665664621805805 17580797558874624233177177)
            ·
              refine ⟨13185598169155968174882883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17580797558874624233177177 13185598169155968174882883)
              ·
                refine ⟨19778397253733952262324325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13185598169155968174882883 19778397253733952262324325)
                ·
                  refine ⟨3708449485075116049185811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19778397253733952262324325 3708449485075116049185811)
                  ·
                    refine ⟨5562674227612674073778717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3708449485075116049185811 5562674227612674073778717)
                    ·
                      refine ⟨2086002835354752777667019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5562674227612674073778717 2086002835354752777667019)
                      ·
                        rfl

theorem cell23_4062476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_4062476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062476 prefixEnd_4062476 := by exact prefixLift 4062476
  have htrace : WordTrace (prefixWord ++ tailWord_4062476) baseStart_4062476 baseEnd_4062476 := by
    simpa [prefixWord, tailWord_4062476, baseEnd_4062476] using wordTrace_append hprefix tailTrace_4062476
  have hstable : (prefixWord ++ tailWord_4062476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062476).length < 2 ^ (prefixWord ++ tailWord_4062476).sum := by decide
  have hdescent : baseEnd_4062476 < baseStart_4062476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062569 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 2, 5]
def baseStart_4062569 : Nat := 118140960795 + 4062569 * 2 ^ 59
def prefixEnd_4062569 : Nat := 4983230072969 + 3 ^ 40 * 4062569 * 2
def baseEnd_4062569 : Nat := 695350196351873637934697

theorem tailTrace_4062569 : CollatzResearch.WordTrace tailWord_4062569 prefixEnd_4062569 695350196351873637934697 := by
  unfold tailWord_4062569
  simp only [CollatzResearch.WordTrace]
  refine ⟨148174064419013819391558761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98782709612675879594372507 148174064419013819391558761)
  ·
    refine ⟨111130548314260364543669071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148174064419013819391558761 111130548314260364543669071)
    ·
      refine ⟨166695822471390546815503607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111130548314260364543669071 166695822471390546815503607)
      ·
        refine ⟨250043733707085820223255411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166695822471390546815503607 250043733707085820223255411)
        ·
          refine ⟨375065600560628730334883117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250043733707085820223255411 375065600560628730334883117)
          ·
            refine ⟨140649600210235773875581169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375065600560628730334883117 140649600210235773875581169)
            ·
              refine ⟨105487200157676830406685877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140649600210235773875581169 105487200157676830406685877)
              ·
                refine ⟨9889425014782202850626801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105487200157676830406685877 9889425014782202850626801)
                ·
                  refine ⟨7417068761086652137970101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9889425014782202850626801 7417068761086652137970101)
                  ·
                    refine ⟨695350196351873637934697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7417068761086652137970101 695350196351873637934697)
                    ·
                      rfl

theorem cell23_4062569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_4062569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062569 prefixEnd_4062569 := by exact prefixLift 4062569
  have htrace : WordTrace (prefixWord ++ tailWord_4062569) baseStart_4062569 baseEnd_4062569 := by
    simpa [prefixWord, tailWord_4062569, baseEnd_4062569] using wordTrace_append hprefix tailTrace_4062569
  have hstable : (prefixWord ++ tailWord_4062569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062569).length < 2 ^ (prefixWord ++ tailWord_4062569).sum := by decide
  have hdescent : baseEnd_4062569 < baseStart_4062569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062573 : List Nat := [1, 5, 1, 1, 1, 4, 2, 3, 5]
def baseStart_4062573 : Nat := 118140960795 + 4062573 * 2 ^ 59
def prefixEnd_4062573 : Nat := 4983230072969 + 3 ^ 40 * 4062573 * 2
def baseEnd_4062573 : Nat := 231783626997582099794897

theorem tailTrace_4062573 : CollatzResearch.WordTrace tailWord_4062573 prefixEnd_4062573 231783626997582099794897 := by
  unfold tailWord_4062573
  simp only [CollatzResearch.WordTrace]
  refine ⟨148174210310999328074704373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98782806873999552049802915 148174210310999328074704373)
  ·
    refine ⟨13891332216656187007003535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148174210310999328074704373 13891332216656187007003535)
    ·
      refine ⟨20836998324984280510505303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13891332216656187007003535 20836998324984280510505303)
      ·
        refine ⟨31255497487476420765757955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20836998324984280510505303 31255497487476420765757955)
        ·
          refine ⟨46883246231214631148636933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31255497487476420765757955 46883246231214631148636933)
          ·
            refine ⟨8790608668352743340369425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46883246231214631148636933 8790608668352743340369425)
            ·
              refine ⟨6592956501264557505277069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8790608668352743340369425 6592956501264557505277069)
              ·
                refine ⟨2472358687974209064478901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6592956501264557505277069 2472358687974209064478901)
                ·
                  refine ⟨231783626997582099794897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2472358687974209064478901 231783626997582099794897)
                  ·
                    rfl

theorem cell23_4062573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_4062573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062573 prefixEnd_4062573 := by exact prefixLift 4062573
  have htrace : WordTrace (prefixWord ++ tailWord_4062573) baseStart_4062573 baseEnd_4062573 := by
    simpa [prefixWord, tailWord_4062573, baseEnd_4062573] using wordTrace_append hprefix tailTrace_4062573
  have hstable : (prefixWord ++ tailWord_4062573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062573).length < 2 ^ (prefixWord ++ tailWord_4062573).sum := by decide
  have hdescent : baseEnd_4062573 < baseStart_4062573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062590 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_4062590 : Nat := 118140960795 + 4062590 * 2 ^ 59
def prefixEnd_4062590 : Nat := 4983230072969 + 3 ^ 40 * 4062590 * 2
def baseEnd_4062590 : Nat := 231784596905485036849055

theorem tailTrace_4062590 : CollatzResearch.WordTrace tailWord_4062590 prefixEnd_4062590 231784596905485036849055 := by
  unfold tailWord_4062590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18521853793992217497259153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98783220234625159985382149 18521853793992217497259153)
  ·
    refine ⟨13891390345494163122944365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18521853793992217497259153 13891390345494163122944365)
    ·
      refine ⟨5209271379560311171104137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13891390345494163122944365 5209271379560311171104137)
      ·
        refine ⟨3906953534670233378328103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5209271379560311171104137 3906953534670233378328103)
        ·
          refine ⟨5860430302005350067492155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906953534670233378328103 5860430302005350067492155)
          ·
            refine ⟨8790645453008025101238233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860430302005350067492155 8790645453008025101238233)
            ·
              refine ⟨6592984089756018825928675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8790645453008025101238233 6592984089756018825928675)
              ·
                refine ⟨9889476134634028238893013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592984089756018825928675 9889476134634028238893013)
                ·
                  refine ⟨231784596905485036849055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9889476134634028238893013 231784596905485036849055)
                  ·
                    rfl

theorem cell23_4062590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_4062590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062590 prefixEnd_4062590 := by exact prefixLift 4062590
  have htrace : WordTrace (prefixWord ++ tailWord_4062590) baseStart_4062590 baseEnd_4062590 := by
    simpa [prefixWord, tailWord_4062590, baseEnd_4062590] using wordTrace_append hprefix tailTrace_4062590
  have hstable : (prefixWord ++ tailWord_4062590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062590).length < 2 ^ (prefixWord ++ tailWord_4062590).sum := by decide
  have hdescent : baseEnd_4062590 < baseStart_4062590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062701 : List Nat := [1, 5, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_4062701 : Nat := 118140960795 + 4062701 * 2 ^ 59
def prefixEnd_4062701 : Nat := 4983230072969 + 3 ^ 40 * 4062701 * 2
def baseEnd_4062701 : Nat := 695372789500671465784495

theorem tailTrace_4062701 : CollatzResearch.WordTrace tailWord_4062701 prefixEnd_4062701 695372789500671465784495 := by
  unfold tailWord_4062701
  simp only [CollatzResearch.WordTrace]
  refine ⟨148178878854535605935363957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98785919236357070623575971 148178878854535605935363957)
  ·
    refine ⟨13891769892612713056440371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148178878854535605935363957 13891769892612713056440371)
    ·
      refine ⟨20837654838919069584660557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13891769892612713056440371 20837654838919069584660557)
      ·
        refine ⟨7814120564594651094247709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20837654838919069584660557 7814120564594651094247709)
        ·
          refine ⟨2930295211722994160342891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7814120564594651094247709 2930295211722994160342891)
          ·
            refine ⟨4395442817584491240514337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930295211722994160342891 4395442817584491240514337)
            ·
              refine ⟨3296582113188368430385753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4395442817584491240514337 3296582113188368430385753)
              ·
                refine ⟨2472436584891276322789315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3296582113188368430385753 2472436584891276322789315)
                ·
                  refine ⟨3708654877336914484183973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472436584891276322789315 3708654877336914484183973)
                  ·
                    refine ⟨695372789500671465784495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708654877336914484183973 695372789500671465784495)
                    ·
                      rfl

theorem cell23_4062701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_4062701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062701 prefixEnd_4062701 := by exact prefixLift 4062701
  have htrace : WordTrace (prefixWord ++ tailWord_4062701) baseStart_4062701 baseEnd_4062701 := by
    simpa [prefixWord, tailWord_4062701, baseEnd_4062701] using wordTrace_append hprefix tailTrace_4062701
  have hstable : (prefixWord ++ tailWord_4062701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062701).length < 2 ^ (prefixWord ++ tailWord_4062701).sum := by decide
  have hdescent : baseEnd_4062701 < baseStart_4062701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062716 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_4062716 : Nat := 118140960795 + 4062716 * 2 ^ 59
def prefixEnd_4062716 : Nat := 4983230072969 + 3 ^ 40 * 4062716 * 2
def baseEnd_4062716 : Nat := 2086126070711831838665915

theorem tailTrace_4062716 : CollatzResearch.WordTrace tailWord_4062716 prefixEnd_4062716 2086126070711831838665915 := by
  unfold tailWord_4062716
  simp only [CollatzResearch.WordTrace]
  refine ⟨74089712974740631748580001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98786283966320842331440001 74089712974740631748580001)
  ·
    refine ⟨55567284731055473811435001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74089712974740631748580001 55567284731055473811435001)
    ·
      refine ⟨41675463548291605358576251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55567284731055473811435001 41675463548291605358576251)
      ·
        refine ⟨62513195322437408037864377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41675463548291605358576251 62513195322437408037864377)
        ·
          refine ⟨46884896491828056028398283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62513195322437408037864377 46884896491828056028398283)
          ·
            refine ⟨70327344737742084042597425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46884896491828056028398283 70327344737742084042597425)
            ·
              refine ⟨52745508553306563031948069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70327344737742084042597425 52745508553306563031948069)
              ·
                refine ⟨9889782853744980568490263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52745508553306563031948069 9889782853744980568490263)
                ·
                  refine ⟨14834674280617470852735395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9889782853744980568490263 14834674280617470852735395)
                  ·
                    refine ⟨22252011420926206279103093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14834674280617470852735395 22252011420926206279103093)
                    ·
                      refine ⟨2086126070711831838665915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22252011420926206279103093 2086126070711831838665915)
                      ·
                        rfl

theorem cell23_4062716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_4062716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062716 prefixEnd_4062716 := by exact prefixLift 4062716
  have htrace : WordTrace (prefixWord ++ tailWord_4062716) baseStart_4062716 baseEnd_4062716 := by
    simpa [prefixWord, tailWord_4062716, baseEnd_4062716] using wordTrace_append hprefix tailTrace_4062716
  have hstable : (prefixWord ++ tailWord_4062716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062716).length < 2 ^ (prefixWord ++ tailWord_4062716).sum := by decide
  have hdescent : baseEnd_4062716 < baseStart_4062716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062719 : List Nat := [1, 1, 2, 2, 1, 2, 2, 12]
def baseStart_4062719 : Nat := 118140960795 + 4062719 * 2 ^ 59
def prefixEnd_4062719 : Nat := 4983230072969 + 3 ^ 40 * 4062719 * 2
def baseEnd_4062719 : Nat := 77263985598288715812163

theorem tailTrace_4062719 : CollatzResearch.WordTrace tailWord_4062719 prefixEnd_4062719 77263985598288715812163 := by
  unfold tailWord_4062719
  simp only [CollatzResearch.WordTrace]
  refine ⟨148179535368470395009519211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98786356912313596673012807 148179535368470395009519211)
  ·
    refine ⟨222269303052705592514278817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148179535368470395009519211 222269303052705592514278817)
    ·
      refine ⟨166701977289529194385709113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222269303052705592514278817 166701977289529194385709113)
      ·
        refine ⟨125026482967146895789281835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166701977289529194385709113 125026482967146895789281835)
        ·
          refine ⟨187539724450720343683922753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125026482967146895789281835 187539724450720343683922753)
          ·
            refine ⟨140654793338040257762942065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187539724450720343683922753 140654793338040257762942065)
            ·
              refine ⟨105491095003530193322206549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140654793338040257762942065 105491095003530193322206549)
              ·
                refine ⟨77263985598288715812163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 105491095003530193322206549 77263985598288715812163)
                ·
                  rfl

theorem cell23_4062719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 12].length) (baseStart_4062719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062719 prefixEnd_4062719 := by exact prefixLift 4062719
  have htrace : WordTrace (prefixWord ++ tailWord_4062719) baseStart_4062719 baseEnd_4062719 := by
    simpa [prefixWord, tailWord_4062719, baseEnd_4062719] using wordTrace_append hprefix tailTrace_4062719
  have hstable : (prefixWord ++ tailWord_4062719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062719).length < 2 ^ (prefixWord ++ tailWord_4062719).sum := by decide
  have hdescent : baseEnd_4062719 < baseStart_4062719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062730 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_4062730 : Nat := 118140960795 + 4062730 * 2 ^ 59
def prefixEnd_4062730 : Nat := 4983230072969 + 3 ^ 40 * 4062730 * 2
def baseEnd_4062730 : Nat := 2086133259440994783890851

theorem tailTrace_4062730 : CollatzResearch.WordTrace tailWord_4062730 prefixEnd_4062730 2086133259440994783890851 := by
  unfold tailWord_4062730
  simp only [CollatzResearch.WordTrace]
  refine ⟨37044984142857635972042411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98786624380953695925446429 37044984142857635972042411)
  ·
    refine ⟨55567476214286453958063617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37044984142857635972042411 55567476214286453958063617)
    ·
      refine ⟨41675607160714840468547713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55567476214286453958063617 41675607160714840468547713)
      ·
        refine ⟨31256705370536130351410785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41675607160714840468547713 31256705370536130351410785)
        ·
          refine ⟨23442529027902097763558089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31256705370536130351410785 23442529027902097763558089)
          ·
            refine ⟨17581896770926573322668567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23442529027902097763558089 17581896770926573322668567)
            ·
              refine ⟨26372845156389859984002851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17581896770926573322668567 26372845156389859984002851)
              ·
                refine ⟨39559267734584789976004277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26372845156389859984002851 39559267734584789976004277)
                ·
                  refine ⟨3708681350117324060250401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39559267734584789976004277 3708681350117324060250401)
                  ·
                    refine ⟨2781511012587993045187801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3708681350117324060250401 2781511012587993045187801)
                    ·
                      refine ⟨2086133259440994783890851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781511012587993045187801 2086133259440994783890851)
                      ·
                        rfl

theorem cell23_4062730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_4062730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062730 prefixEnd_4062730 := by exact prefixLift 4062730
  have htrace : WordTrace (prefixWord ++ tailWord_4062730) baseStart_4062730 baseEnd_4062730 := by
    simpa [prefixWord, tailWord_4062730, baseEnd_4062730] using wordTrace_append hprefix tailTrace_4062730
  have hstable : (prefixWord ++ tailWord_4062730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062730).length < 2 ^ (prefixWord ++ tailWord_4062730).sum := by decide
  have hdescent : baseEnd_4062730 < baseStart_4062730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062734 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_4062734 : Nat := 118140960795 + 4062734 * 2 ^ 59
def prefixEnd_4062734 : Nat := 4983230072969 + 3 ^ 40 * 4062734 * 2
def baseEnd_4062734 : Nat := 2086135313363612768240833

theorem tailTrace_4062734 : CollatzResearch.WordTrace tailWord_4062734 prefixEnd_4062734 2086135313363612768240833 := by
  unfold tailWord_4062734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18522510307927006571414407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98786721642277368380876837 18522510307927006571414407)
  ·
    refine ⟨27783765461890509857121611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18522510307927006571414407 27783765461890509857121611)
    ·
      refine ⟨41675648192835764785682417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27783765461890509857121611 41675648192835764785682417)
      ·
        refine ⟨31256736144626823589261813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41675648192835764785682417 31256736144626823589261813)
        ·
          refine ⟨2930319013558764711493295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31256736144626823589261813 2930319013558764711493295)
          ·
            refine ⟨4395478520338147067239943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930319013558764711493295 4395478520338147067239943)
            ·
              refine ⟨6593217780507220600859915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395478520338147067239943 6593217780507220600859915)
              ·
                refine ⟨9889826670760830901289873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593217780507220600859915 9889826670760830901289873)
                ·
                  refine ⟨7417370003070623175967405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9889826670760830901289873 7417370003070623175967405)
                  ·
                    refine ⟨2781513751151483690987777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7417370003070623175967405 2781513751151483690987777)
                    ·
                      refine ⟨2086135313363612768240833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781513751151483690987777 2086135313363612768240833)
                      ·
                        rfl

theorem cell23_4062734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_4062734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062734 prefixEnd_4062734 := by exact prefixLift 4062734
  have htrace : WordTrace (prefixWord ++ tailWord_4062734) baseStart_4062734 baseEnd_4062734 := by
    simpa [prefixWord, tailWord_4062734, baseEnd_4062734] using wordTrace_append hprefix tailTrace_4062734
  have hstable : (prefixWord ++ tailWord_4062734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062734).length < 2 ^ (prefixWord ++ tailWord_4062734).sum := by decide
  have hdescent : baseEnd_4062734 < baseStart_4062734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062774 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_4062774 : Nat := 118140960795 + 4062774 * 2 ^ 59
def prefixEnd_4062774 : Nat := 4983230072969 + 3 ^ 40 * 4062774 * 2
def baseEnd_4062774 : Nat := 695385284196597537246883

theorem tailTrace_4062774 : CollatzResearch.WordTrace tailWord_4062774 prefixEnd_4062774 695385284196597537246883 := by
  unfold tailWord_4062774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9261346336454446212673211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98787694255514092935180917 9261346336454446212673211)
  ·
    refine ⟨13892019504681669319009817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9261346336454446212673211 13892019504681669319009817)
    ·
      refine ⟨10419014628511251989257363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13892019504681669319009817 10419014628511251989257363)
      ·
        refine ⟨15628521942766877983886045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10419014628511251989257363 15628521942766877983886045)
        ·
          refine ⟨5860695728537579243957267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15628521942766877983886045 5860695728537579243957267)
          ·
            refine ⟨8791043592806368865935901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860695728537579243957267 8791043592806368865935901)
            ·
              refine ⟨3296641347302388324725963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8791043592806368865935901 3296641347302388324725963)
              ·
                refine ⟨4944962020953582487088945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296641347302388324725963 4944962020953582487088945)
                ·
                  refine ⟨3708721515715186865316709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4944962020953582487088945 3708721515715186865316709)
                  ·
                    refine ⟨695385284196597537246883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708721515715186865316709 695385284196597537246883)
                    ·
                      rfl

theorem cell23_4062774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_4062774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062774 prefixEnd_4062774 := by exact prefixLift 4062774
  have htrace : WordTrace (prefixWord ++ tailWord_4062774) baseStart_4062774 baseEnd_4062774 := by
    simpa [prefixWord, tailWord_4062774, baseEnd_4062774] using wordTrace_append hprefix tailTrace_4062774
  have hstable : (prefixWord ++ tailWord_4062774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062774).length < 2 ^ (prefixWord ++ tailWord_4062774).sum := by decide
  have hdescent : baseEnd_4062774 < baseStart_4062774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062863 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 3, 7, 2]
def baseStart_4062863 : Nat := 118140960795 + 4062863 * 2 ^ 59
def prefixEnd_4062863 : Nat := 4983230072969 + 3 ^ 40 * 4062863 * 2
def baseEnd_4062863 : Nat := 2086201552368042763527739

theorem tailTrace_4062863 : CollatzResearch.WordTrace tailWord_4062863 prefixEnd_4062863 2086201552368042763527739 := by
  unfold tailWord_4062863
  simp only [CollatzResearch.WordTrace]
  refine ⟨148184787479948707602761243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98789858319965805068507495 148184787479948707602761243)
  ·
    refine ⟨222277181219923061404141865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148184787479948707602761243 222277181219923061404141865)
    ·
      refine ⟨166707885914942296053106399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222277181219923061404141865 166707885914942296053106399)
      ·
        refine ⟨250061828872413444079659599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166707885914942296053106399 250061828872413444079659599)
        ·
          refine ⟨375092743308620166119489399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250061828872413444079659599 375092743308620166119489399)
          ·
            refine ⟨562639114962930249179234099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375092743308620166119489399 562639114962930249179234099)
            ·
              refine ⟨843958672444395373768851149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562639114962930249179234099 843958672444395373768851149)
              ·
                refine ⟨316484502166648265163319181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843958672444395373768851149 316484502166648265163319181)
                ·
                  refine ⟨118681688312493099436244693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316484502166648265163319181 118681688312493099436244693)
                  ·
                    refine ⟨2781602069824057018036985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 118681688312493099436244693 2781602069824057018036985)
                    ·
                      refine ⟨2086201552368042763527739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781602069824057018036985 2086201552368042763527739)
                      ·
                        rfl

theorem cell23_4062863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 7, 2].length) (baseStart_4062863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062863 prefixEnd_4062863 := by exact prefixLift 4062863
  have htrace : WordTrace (prefixWord ++ tailWord_4062863) baseStart_4062863 baseEnd_4062863 := by
    simpa [prefixWord, tailWord_4062863, baseEnd_4062863] using wordTrace_append hprefix tailTrace_4062863
  have hstable : (prefixWord ++ tailWord_4062863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062863).length < 2 ^ (prefixWord ++ tailWord_4062863).sum := by decide
  have hdescent : baseEnd_4062863 < baseStart_4062863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062880 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 2, 5, 2]
def baseStart_4062880 : Nat := 118140960795 + 4062880 * 2 ^ 59
def prefixEnd_4062880 : Nat := 4983230072969 + 3 ^ 40 * 4062880 * 2
def baseEnd_4062880 : Nat := 2086210281539169197015161

theorem tailTrace_4062880 : CollatzResearch.WordTrace tailWord_4062880 prefixEnd_4062880 2086210281539169197015161 := by
  unfold tailWord_4062880
  simp only [CollatzResearch.WordTrace]
  refine ⟨74092703760443559753065047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98790271680591413004086729 74092703760443559753065047)
  ·
    refine ⟨111139055640665339629597571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74092703760443559753065047 111139055640665339629597571)
    ·
      refine ⟨166708583460998009444396357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111139055640665339629597571 166708583460998009444396357)
      ·
        refine ⟨31257859398937126770824317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166708583460998009444396357 31257859398937126770824317)
        ·
          refine ⟨11721697274601422539059119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31257859398937126770824317 11721697274601422539059119)
          ·
            refine ⟨17582545911902133808588679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11721697274601422539059119 17582545911902133808588679)
            ·
              refine ⟨26373818867853200712883019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17582545911902133808588679 26373818867853200712883019)
              ·
                refine ⟨39560728301779801069324529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26373818867853200712883019 39560728301779801069324529)
                ·
                  refine ⟨29670546226334850801993397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39560728301779801069324529 29670546226334850801993397)
                  ·
                    refine ⟨2781613708718892262686881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29670546226334850801993397 2781613708718892262686881)
                    ·
                      refine ⟨2086210281539169197015161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781613708718892262686881 2086210281539169197015161)
                      ·
                        rfl

theorem cell23_4062880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_4062880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062880 prefixEnd_4062880 := by exact prefixLift 4062880
  have htrace : WordTrace (prefixWord ++ tailWord_4062880) baseStart_4062880 baseEnd_4062880 := by
    simpa [prefixWord, tailWord_4062880, baseEnd_4062880] using wordTrace_append hprefix tailTrace_4062880
  have hstable : (prefixWord ++ tailWord_4062880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062880).length < 2 ^ (prefixWord ++ tailWord_4062880).sum := by decide
  have hdescent : baseEnd_4062880 < baseStart_4062880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062910 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_4062910 : Nat := 118140960795 + 4062910 * 2 ^ 59
def prefixEnd_4062910 : Nat := 4983230072969 + 3 ^ 40 * 4062910 * 2
def baseEnd_4062910 : Nat := 2086225685958804079640023

theorem tailTrace_4062910 : CollatzResearch.WordTrace tailWord_4062910 prefixEnd_4062910 2086225685958804079640023 := by
  unfold tailWord_4062910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18523312713847304328715273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98791001140518956419814789 18523312713847304328715273)
  ·
    refine ⟨13892484535385478246536455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18523312713847304328715273 13892484535385478246536455)
    ·
      refine ⟨20838726803078217369804683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13892484535385478246536455 20838726803078217369804683)
      ·
        refine ⟨31258090204617326054707025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20838726803078217369804683 31258090204617326054707025)
        ·
          refine ⟨23443567653462994541030269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31258090204617326054707025 23443567653462994541030269)
          ·
            refine ⟨8791337870048622952886351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23443567653462994541030269 8791337870048622952886351)
            ·
              refine ⟨13187006805072934429329527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8791337870048622952886351 13187006805072934429329527)
              ·
                refine ⟨19780510207609401643994291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13187006805072934429329527 19780510207609401643994291)
                ·
                  refine ⟨29670765311414102465991437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19780510207609401643994291 29670765311414102465991437)
                  ·
                    refine ⟨11126536991780288424746789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29670765311414102465991437 11126536991780288424746789)
                    ·
                      refine ⟨2086225685958804079640023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11126536991780288424746789 2086225685958804079640023)
                      ·
                        rfl

theorem cell23_4062910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_4062910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062910 prefixEnd_4062910 := by exact prefixLift 4062910
  have htrace : WordTrace (prefixWord ++ tailWord_4062910) baseStart_4062910 baseEnd_4062910 := by
    simpa [prefixWord, tailWord_4062910, baseEnd_4062910] using wordTrace_append hprefix tailTrace_4062910
  have hstable : (prefixWord ++ tailWord_4062910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062910).length < 2 ^ (prefixWord ++ tailWord_4062910).sum := by decide
  have hdescent : baseEnd_4062910 < baseStart_4062910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062937 : List Nat := [1, 2, 1, 2, 3, 3, 2, 4, 1, 4]
def baseStart_4062937 : Nat := 118140960795 + 4062937 * 2 ^ 59
def prefixEnd_4062937 : Nat := 4983230072969 + 3 ^ 40 * 4062937 * 2
def baseEnd_4062937 : Nat := 695413183312158491334133

theorem tailTrace_4062937 : CollatzResearch.WordTrace tailWord_4062937 prefixEnd_4062937 695413183312158491334133 := by
  unfold tailWord_4062937
  simp only [CollatzResearch.WordTrace]
  refine ⟨148187486481680618240955065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98791657654453745493970043 148187486481680618240955065)
  ·
    refine ⟨111140614861260463680716299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148187486481680618240955065 111140614861260463680716299)
    ·
      refine ⟨166710922291890695521074449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111140614861260463680716299 166710922291890695521074449)
      ·
        refine ⟨125033191718918021640805837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166710922291890695521074449 125033191718918021640805837)
        ·
          refine ⟨46887446894594258115302189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125033191718918021640805837 46887446894594258115302189)
          ·
            refine ⟨17582792585472846793238321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46887446894594258115302189 17582792585472846793238321)
            ·
              refine ⟨13187094439104635094928741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17582792585472846793238321 13187094439104635094928741)
              ·
                refine ⟨2472580207332119080299139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13187094439104635094928741 2472580207332119080299139)
                ·
                  refine ⟨3708870310998178620448709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472580207332119080299139 3708870310998178620448709)
                  ·
                    refine ⟨695413183312158491334133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3708870310998178620448709 695413183312158491334133)
                    ·
                      rfl

theorem cell23_4062937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 4].length) (baseStart_4062937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062937 prefixEnd_4062937 := by exact prefixLift 4062937
  have htrace : WordTrace (prefixWord ++ tailWord_4062937) baseStart_4062937 baseEnd_4062937 := by
    simpa [prefixWord, tailWord_4062937, baseEnd_4062937] using wordTrace_append hprefix tailTrace_4062937
  have hstable : (prefixWord ++ tailWord_4062937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062937).length < 2 ^ (prefixWord ++ tailWord_4062937).sum := by decide
  have hdescent : baseEnd_4062937 < baseStart_4062937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062960 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 5, 1, 3]
def baseStart_4062960 : Nat := 118140960795 + 4062960 * 2 ^ 59
def prefixEnd_4062960 : Nat := 4983230072969 + 3 ^ 40 * 4062960 * 2
def baseEnd_4062960 : Nat := 2086251359991528884014793

theorem tailTrace_4062960 : CollatzResearch.WordTrace tailWord_4062960 prefixEnd_4062960 2086251359991528884014793 := by
  unfold tailWord_4062960
  simp only [CollatzResearch.WordTrace]
  refine ⟨74094162680298646584521167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98792216907064862112694889 74094162680298646584521167)
  ·
    refine ⟨111141244020447969876781751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74094162680298646584521167 111141244020447969876781751)
    ·
      refine ⟨166711866030671954815172627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111141244020447969876781751 166711866030671954815172627)
      ·
        refine ⟨250067799046007932222758941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166711866030671954815172627 250067799046007932222758941)
        ·
          refine ⟨93775424642252974583534603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250067799046007932222758941 93775424642252974583534603)
          ·
            refine ⟨140663136963379461875301905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93775424642252974583534603 140663136963379461875301905)
            ·
              refine ⟨105497352722534596406476429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140663136963379461875301905 105497352722534596406476429)
              ·
                refine ⟨39561507270950473652428661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105497352722534596406476429 39561507270950473652428661)
                ·
                  refine ⟨3708891306651606904915187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39561507270950473652428661 3708891306651606904915187)
                  ·
                    refine ⟨5563336959977410357372781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3708891306651606904915187 5563336959977410357372781)
                    ·
                      refine ⟨2086251359991528884014793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5563336959977410357372781 2086251359991528884014793)
                      ·
                        rfl

theorem cell23_4062960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 1, 3].length) (baseStart_4062960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062960 prefixEnd_4062960 := by exact prefixLift 4062960
  have htrace : WordTrace (prefixWord ++ tailWord_4062960) baseStart_4062960 baseEnd_4062960 := by
    simpa [prefixWord, tailWord_4062960, baseEnd_4062960] using wordTrace_append hprefix tailTrace_4062960
  have hstable : (prefixWord ++ tailWord_4062960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062960).length < 2 ^ (prefixWord ++ tailWord_4062960).sum := by decide
  have hdescent : baseEnd_4062960 < baseStart_4062960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062963 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 3, 5]
def baseStart_4062963 : Nat := 118140960795 + 4062963 * 2 ^ 59
def prefixEnd_4062963 : Nat := 4983230072969 + 3 ^ 40 * 4062963 * 2
def baseEnd_4062963 : Nat := 695417633477830790759093

theorem tailTrace_4062963 : CollatzResearch.WordTrace tailWord_4062963 prefixEnd_4062963 695417633477830790759093 := by
  unfold tailWord_4062963
  simp only [CollatzResearch.WordTrace]
  refine ⟨148188434779586424681401543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98792289853057616454267695 148188434779586424681401543)
  ·
    refine ⟨222282652169379637022102315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148188434779586424681401543 222282652169379637022102315)
    ·
      refine ⟨333423978254069455533153473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222282652169379637022102315 333423978254069455533153473)
      ·
        refine ⟨250067983690552091649865105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333423978254069455533153473 250067983690552091649865105)
        ·
          refine ⟨187550987767914068737398829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250067983690552091649865105 187550987767914068737398829)
          ·
            refine ⟨70331620412967775776524561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187550987767914068737398829 70331620412967775776524561)
            ·
              refine ⟨52748715309725831832393421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70331620412967775776524561 52748715309725831832393421)
              ·
                refine ⟨19780768241147186937147533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52748715309725831832393421 19780768241147186937147533)
                ·
                  refine ⟨7417788090430195101430325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19780768241147186937147533 7417788090430195101430325)
                  ·
                    refine ⟨695417633477830790759093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7417788090430195101430325 695417633477830790759093)
                    ·
                      rfl

theorem cell23_4062963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 5].length) (baseStart_4062963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062963 prefixEnd_4062963 := by exact prefixLift 4062963
  have htrace : WordTrace (prefixWord ++ tailWord_4062963) baseStart_4062963 baseEnd_4062963 := by
    simpa [prefixWord, tailWord_4062963, baseEnd_4062963] using wordTrace_append hprefix tailTrace_4062963
  have hstable : (prefixWord ++ tailWord_4062963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062963).length < 2 ^ (prefixWord ++ tailWord_4062963).sum := by decide
  have hdescent : baseEnd_4062963 < baseStart_4062963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062964 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4062964 : Nat := 118140960795 + 4062964 * 2 ^ 59
def prefixEnd_4062964 : Nat := 4983230072969 + 3 ^ 40 * 4062964 * 2
def baseEnd_4062964 : Nat := 2086253413914146868364775

theorem tailTrace_4062964 : CollatzResearch.WordTrace tailWord_4062964 prefixEnd_4062964 2086253413914146868364775 := by
  unfold tailWord_4062964
  simp only [CollatzResearch.WordTrace]
  refine ⟨74094235626291400926093973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98792314168388534568125297 74094235626291400926093973)
  ·
    refine ⟨3473167294982409418410655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74094235626291400926093973 3473167294982409418410655)
    ·
      refine ⟨5209750942473614127615983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3473167294982409418410655 5209750942473614127615983)
      ·
        refine ⟨7814626413710421191423975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5209750942473614127615983 7814626413710421191423975)
        ·
          refine ⟨11721939620565631787135963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814626413710421191423975 11721939620565631787135963)
          ·
            refine ⟨17582909430848447680703945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11721939620565631787135963 17582909430848447680703945)
            ·
              refine ⟨13187182073136335760527959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17582909430848447680703945 13187182073136335760527959)
              ·
                refine ⟨19780773109704503640791939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13187182073136335760527959 19780773109704503640791939)
                ·
                  refine ⟨29671159664556755461187909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19780773109704503640791939 29671159664556755461187909)
                  ·
                    refine ⟨5563342437104391648972733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29671159664556755461187909 5563342437104391648972733)
                    ·
                      refine ⟨2086253413914146868364775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5563342437104391648972733 2086253413914146868364775)
                      ·
                        rfl

theorem cell23_4062964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4062964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4062964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4062964 prefixEnd_4062964 := by exact prefixLift 4062964
  have htrace : WordTrace (prefixWord ++ tailWord_4062964) baseStart_4062964 baseEnd_4062964 := by
    simpa [prefixWord, tailWord_4062964, baseEnd_4062964] using wordTrace_append hprefix tailTrace_4062964
  have hstable : (prefixWord ++ tailWord_4062964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062964).length < 2 ^ (prefixWord ++ tailWord_4062964).sum := by decide
  have hdescent : baseEnd_4062964 < baseStart_4062964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063010 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_4063010 : Nat := 118140960795 + 4063010 * 2 ^ 59
def prefixEnd_4063010 : Nat := 4983230072969 + 3 ^ 40 * 4063010 * 2
def baseEnd_4063010 : Nat := 695425678008084562796521

theorem tailTrace_4063010 : CollatzResearch.WordTrace tailWord_4063010 prefixEnd_4063010 695425678008084562796521 := by
  unfold tailWord_4063010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37047537252604037927090621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98793432673610767805574989 37047537252604037927090621)
  ·
    refine ⟨13892826469726514222658983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37047537252604037927090621 13892826469726514222658983)
    ·
      refine ⟨20839239704589771333988475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13892826469726514222658983 20839239704589771333988475)
      ·
        refine ⟨31258859556884657000982713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20839239704589771333988475 31258859556884657000982713)
        ·
          refine ⟨23444144667663492750737035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31258859556884657000982713 23444144667663492750737035)
          ·
            refine ⟨35166217001495239126105553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23444144667663492750737035 35166217001495239126105553)
            ·
              refine ⟨26374662751121429344579165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35166217001495239126105553 26374662751121429344579165)
              ·
                refine ⟨9890498531670536004217187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26374662751121429344579165 9890498531670536004217187)
                ·
                  refine ⟨14835747797505804006325781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9890498531670536004217187 14835747797505804006325781)
                  ·
                    refine ⟨695425678008084562796521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14835747797505804006325781 695425678008084562796521)
                    ·
                      rfl

theorem cell23_4063010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_4063010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063010 prefixEnd_4063010 := by exact prefixLift 4063010
  have htrace : WordTrace (prefixWord ++ tailWord_4063010) baseStart_4063010 baseEnd_4063010 := by
    simpa [prefixWord, tailWord_4063010, baseEnd_4063010] using wordTrace_append hprefix tailTrace_4063010
  have hstable : (prefixWord ++ tailWord_4063010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063010).length < 2 ^ (prefixWord ++ tailWord_4063010).sum := by decide
  have hdescent : baseEnd_4063010 < baseStart_4063010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063034 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4]
def baseStart_4063034 : Nat := 118140960795 + 4063034 * 2 ^ 59
def prefixEnd_4063034 : Nat := 4983230072969 + 3 ^ 40 * 4063034 * 2
def baseEnd_4063034 : Nat := 2086289357559961594489453

theorem tailTrace_4063034 : CollatzResearch.WordTrace tailWord_4063034 prefixEnd_4063034 2086289357559961594489453 := by
  unfold tailWord_4063034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37047756090582300951809039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98794016241552802538157437 37047756090582300951809039)
  ·
    refine ⟨55571634135873451427713559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37047756090582300951809039 55571634135873451427713559)
    ·
      refine ⟨83357451203810177141570339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55571634135873451427713559 83357451203810177141570339)
      ·
        refine ⟨125036176805715265712355509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83357451203810177141570339 125036176805715265712355509)
        ·
          refine ⟨11722141575535806160533329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125036176805715265712355509 11722141575535806160533329)
          ·
            refine ⟨8791606181651854620399997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11722141575535806160533329 8791606181651854620399997)
            ·
              refine ⟨3296852318119445482649999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8791606181651854620399997 3296852318119445482649999)
              ·
                refine ⟨4945278477179168223974999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296852318119445482649999 4945278477179168223974999)
                ·
                  refine ⟨7417917715768752335962499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945278477179168223974999 7417917715768752335962499)
                  ·
                    refine ⟨11126876573653128503943749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7417917715768752335962499 11126876573653128503943749)
                    ·
                      refine ⟨2086289357559961594489453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11126876573653128503943749 2086289357559961594489453)
                      ·
                        rfl

theorem cell23_4063034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_4063034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063034 prefixEnd_4063034 := by exact prefixLift 4063034
  have htrace : WordTrace (prefixWord ++ tailWord_4063034) baseStart_4063034 baseEnd_4063034 := by
    simpa [prefixWord, tailWord_4063034, baseEnd_4063034] using wordTrace_append hprefix tailTrace_4063034
  have hstable : (prefixWord ++ tailWord_4063034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063034).length < 2 ^ (prefixWord ++ tailWord_4063034).sum := by decide
  have hdescent : baseEnd_4063034 < baseStart_4063034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063037 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4063037 : Nat := 118140960795 + 4063037 * 2 ^ 59
def prefixEnd_4063037 : Nat := 4983230072969 + 3 ^ 40 * 4063037 * 2
def baseEnd_4063037 : Nat := 2086290898001925082751939

theorem tailTrace_4063037 : CollatzResearch.WordTrace tailWord_4063037 prefixEnd_4063037 2086290898001925082751939 := by
  unfold tailWord_4063037
  simp only [CollatzResearch.WordTrace]
  refine ⟨148191133781318335319595365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98794089187545556879730243 148191133781318335319595365)
  ·
    refine ⟨27785837583997187872424131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148191133781318335319595365 27785837583997187872424131)
    ·
      refine ⟨41678756375995781808636197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27785837583997187872424131 41678756375995781808636197)
      ·
        refine ⟨7814766820499209089119287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41678756375995781808636197 7814766820499209089119287)
        ·
          refine ⟨11722150230748813633678931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814766820499209089119287 11722150230748813633678931)
          ·
            refine ⟨17583225346123220450518397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722150230748813633678931 17583225346123220450518397)
            ·
              refine ⟨6593709504796207668944399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17583225346123220450518397 6593709504796207668944399)
              ·
                refine ⟨9890564257194311503416599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593709504796207668944399 9890564257194311503416599)
                ·
                  refine ⟨14835846385791467255124899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9890564257194311503416599 14835846385791467255124899)
                  ·
                    refine ⟨22253769578687200882687349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14835846385791467255124899 22253769578687200882687349)
                    ·
                      refine ⟨2086290898001925082751939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22253769578687200882687349 2086290898001925082751939)
                      ·
                        rfl

theorem cell23_4063037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4063037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063037 prefixEnd_4063037 := by exact prefixLift 4063037
  have htrace : WordTrace (prefixWord ++ tailWord_4063037) baseStart_4063037 baseEnd_4063037 := by
    simpa [prefixWord, tailWord_4063037, baseEnd_4063037] using wordTrace_append hprefix tailTrace_4063037
  have hstable : (prefixWord ++ tailWord_4063037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063037).length < 2 ^ (prefixWord ++ tailWord_4063037).sum := by decide
  have hdescent : baseEnd_4063037 < baseStart_4063037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063050 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_4063050 : Nat := 118140960795 + 4063050 * 2 ^ 59
def prefixEnd_4063050 : Nat := 4983230072969 + 3 ^ 40 * 4063050 * 2
def baseEnd_4063050 : Nat := 2086297573250433531889379

theorem tailTrace_4063050 : CollatzResearch.WordTrace tailWord_4063050 prefixEnd_4063050 2086297573250433531889379 := by
  unfold tailWord_4063050
  simp only [CollatzResearch.WordTrace]
  refine ⟨37047901982567809634954651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98794405286847492359879069 37047901982567809634954651)
  ·
    refine ⟨55571852973851714452431977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37047901982567809634954651 55571852973851714452431977)
    ·
      refine ⟨41678889730388785839323983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55571852973851714452431977 41678889730388785839323983)
      ·
        refine ⟨62518334595583178758985975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41678889730388785839323983 62518334595583178758985975)
        ·
          refine ⟨93777501893374768138478963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62518334595583178758985975 93777501893374768138478963)
          ·
            refine ⟨140666252840062152207718445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93777501893374768138478963 140666252840062152207718445)
            ·
              refine ⟨52749844815023307077894417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140666252840062152207718445 52749844815023307077894417)
              ·
                refine ⟨39562383611267480308420813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52749844815023307077894417 39562383611267480308420813)
                ·
                  refine ⟨14835893854225305115657805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39562383611267480308420813 14835893854225305115657805)
                  ·
                    refine ⟨5563460195334489418371677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14835893854225305115657805 5563460195334489418371677)
                    ·
                      refine ⟨2086297573250433531889379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5563460195334489418371677 2086297573250433531889379)
                      ·
                        rfl

theorem cell23_4063050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_4063050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063050 prefixEnd_4063050 := by exact prefixLift 4063050
  have htrace : WordTrace (prefixWord ++ tailWord_4063050) baseStart_4063050 baseEnd_4063050 := by
    simpa [prefixWord, tailWord_4063050, baseEnd_4063050] using wordTrace_append hprefix tailTrace_4063050
  have hstable : (prefixWord ++ tailWord_4063050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063050).length < 2 ^ (prefixWord ++ tailWord_4063050).sum := by decide
  have hdescent : baseEnd_4063050 < baseStart_4063050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063080 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4063080 : Nat := 118140960795 + 4063080 * 2 ^ 59
def prefixEnd_4063080 : Nat := 4983230072969 + 3 ^ 40 * 4063080 * 2
def baseEnd_4063080 : Nat := 2086312977670068414514241

theorem tailTrace_4063080 : CollatzResearch.WordTrace tailWord_4063080 prefixEnd_4063080 2086312977670068414514241 := by
  unfold tailWord_4063080
  simp only [CollatzResearch.WordTrace]
  refine ⟨74096351060081276831705347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98795134746775035775607129 74096351060081276831705347)
  ·
    refine ⟨111144526590121915247558021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74096351060081276831705347 111144526590121915247558021)
    ·
      refine ⟨20839598735647859108917129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111144526590121915247558021 20839598735647859108917129)
      ·
        refine ⟨15629699051735894331687847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20839598735647859108917129 15629699051735894331687847)
        ·
          refine ⟨23444548577603841497531771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15629699051735894331687847 23444548577603841497531771)
          ·
            refine ⟨35166822866405762246297657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23444548577603841497531771 35166822866405762246297657)
            ·
              refine ⟨26375117149804321684723243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35166822866405762246297657 26375117149804321684723243)
              ·
                refine ⟨39562675724706482527084865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26375117149804321684723243 39562675724706482527084865)
                ·
                  refine ⟨29672006793529861895313649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39562675724706482527084865 29672006793529861895313649)
                  ·
                    refine ⟨22254005095147396421485237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29672006793529861895313649 22254005095147396421485237)
                    ·
                      refine ⟨2086312977670068414514241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22254005095147396421485237 2086312977670068414514241)
                      ·
                        rfl

theorem cell23_4063080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4063080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063080 prefixEnd_4063080 := by exact prefixLift 4063080
  have htrace : WordTrace (prefixWord ++ tailWord_4063080) baseStart_4063080 baseEnd_4063080 := by
    simpa [prefixWord, tailWord_4063080, baseEnd_4063080] using wordTrace_append hprefix tailTrace_4063080
  have hstable : (prefixWord ++ tailWord_4063080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063080).length < 2 ^ (prefixWord ++ tailWord_4063080).sum := by decide
  have hdescent : baseEnd_4063080 < baseStart_4063080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063083 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 3, 8]
def baseStart_4063083 : Nat := 118140960795 + 4063083 * 2 ^ 59
def prefixEnd_4063083 : Nat := 4983230072969 + 3 ^ 40 * 4063083 * 2
def baseEnd_4063083 : Nat := 695438172704010634258909

theorem tailTrace_4063083 : CollatzResearch.WordTrace tailWord_4063083 prefixEnd_4063083 695438172704010634258909 := by
  unfold tailWord_4063083
  simp only [CollatzResearch.WordTrace]
  refine ⟨148192811539151685175769903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98795207692767790117179935 148192811539151685175769903)
  ·
    refine ⟨222289217308727527763654855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148192811539151685175769903 222289217308727527763654855)
    ·
      refine ⟨333433825963091291645482283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222289217308727527763654855 333433825963091291645482283)
      ·
        refine ⟨500150738944636937468223425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333433825963091291645482283 500150738944636937468223425)
        ·
          refine ⟨375113054208477703101167569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500150738944636937468223425 375113054208477703101167569)
          ·
            refine ⟨281334790656358277325875677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375113054208477703101167569 281334790656358277325875677)
            ·
              refine ⟨105500546496134353997203379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281334790656358277325875677 105500546496134353997203379)
              ·
                refine ⟨158250819744201530995805069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105500546496134353997203379 158250819744201530995805069)
                ·
                  refine ⟨59344057404075574123426901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158250819744201530995805069 59344057404075574123426901)
                  ·
                    refine ⟨695438172704010634258909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59344057404075574123426901 695438172704010634258909)
                    ·
                      rfl

theorem cell23_4063083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 8].length) (baseStart_4063083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063083 prefixEnd_4063083 := by exact prefixLift 4063083
  have htrace : WordTrace (prefixWord ++ tailWord_4063083) baseStart_4063083 baseEnd_4063083 := by
    simpa [prefixWord, tailWord_4063083, baseEnd_4063083] using wordTrace_append hprefix tailTrace_4063083
  have hstable : (prefixWord ++ tailWord_4063083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063083).length < 2 ^ (prefixWord ++ tailWord_4063083).sum := by decide
  have hdescent : baseEnd_4063083 < baseStart_4063083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063118 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4063118 : Nat := 118140960795 + 4063118 * 2 ^ 59
def prefixEnd_4063118 : Nat := 4983230072969 + 3 ^ 40 * 4063118 * 2
def baseEnd_4063118 : Nat := 2086332489934939265839067

theorem tailTrace_4063118 : CollatzResearch.WordTrace tailWord_4063118 prefixEnd_4063118 2086332489934939265839067 := by
  unfold tailWord_4063118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18524261011753110769161751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98796058729349924102196005 18524261011753110769161751)
  ·
    refine ⟨27786391517629666153742627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18524261011753110769161751 27786391517629666153742627)
    ·
      refine ⟨41679587276444499230613941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27786391517629666153742627 41679587276444499230613941)
      ·
        refine ⟨3907461307166671802870057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41679587276444499230613941 3907461307166671802870057)
        ·
          refine ⟨2930595980375003852152543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3907461307166671802870057 2930595980375003852152543)
          ·
            refine ⟨4395893970562505778228815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930595980375003852152543 4395893970562505778228815)
            ·
              refine ⟨6593840955843758667343223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395893970562505778228815 6593840955843758667343223)
              ·
                refine ⟨9890761433765638001014835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593840955843758667343223 9890761433765638001014835)
                ·
                  refine ⟨14836142150648457001522253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9890761433765638001014835 14836142150648457001522253)
                  ·
                    refine ⟨5563553306493171375570845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14836142150648457001522253 5563553306493171375570845)
                    ·
                      refine ⟨2086332489934939265839067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5563553306493171375570845 2086332489934939265839067)
                      ·
                        rfl

theorem cell23_4063118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4063118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063118 prefixEnd_4063118 := by exact prefixLift 4063118
  have htrace : WordTrace (prefixWord ++ tailWord_4063118) baseStart_4063118 baseEnd_4063118 := by
    simpa [prefixWord, tailWord_4063118, baseEnd_4063118] using wordTrace_append hprefix tailTrace_4063118
  have hstable : (prefixWord ++ tailWord_4063118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063118).length < 2 ^ (prefixWord ++ tailWord_4063118).sum := by decide
  have hdescent : baseEnd_4063118 < baseStart_4063118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063128 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4063128 : Nat := 118140960795 + 4063128 * 2 ^ 59
def prefixEnd_4063128 : Nat := 4983230072969 + 3 ^ 40 * 4063128 * 2
def baseEnd_4063128 : Nat := 2086337624741484226714021

theorem tailTrace_4063128 : CollatzResearch.WordTrace tailWord_4063128 prefixEnd_4063128 2086337624741484226714021 := by
  unfold tailWord_4063128
  simp only [CollatzResearch.WordTrace]
  refine ⟨74097226411994328930579019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98796301882659105240772025 74097226411994328930579019)
  ·
    refine ⟨111145839617991493395868529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74097226411994328930579019 111145839617991493395868529)
    ·
      refine ⟨83359379713493620046901397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111145839617991493395868529 83359379713493620046901397)
      ·
        refine ⟨3907470924070013439698503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83359379713493620046901397 3907470924070013439698503)
        ·
          refine ⟨5861206386105020159547755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907470924070013439698503 5861206386105020159547755)
          ·
            refine ⟨8791809579157530239321633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861206386105020159547755 8791809579157530239321633)
            ·
              refine ⟨6593857184368147679491225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8791809579157530239321633 6593857184368147679491225)
              ·
                refine ⟨4945392888276110759618419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6593857184368147679491225 4945392888276110759618419)
                ·
                  refine ⟨7418089332414166139427629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945392888276110759618419 7418089332414166139427629)
                  ·
                    refine ⟨2781783499655312302285361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7418089332414166139427629 2781783499655312302285361)
                    ·
                      refine ⟨2086337624741484226714021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781783499655312302285361 2086337624741484226714021)
                      ·
                        rfl

theorem cell23_4063128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4063128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063128 prefixEnd_4063128 := by exact prefixLift 4063128
  have htrace : WordTrace (prefixWord ++ tailWord_4063128) baseStart_4063128 baseEnd_4063128 := by
    simpa [prefixWord, tailWord_4063128, baseEnd_4063128] using wordTrace_append hprefix tailTrace_4063128
  have hstable : (prefixWord ++ tailWord_4063128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063128).length < 2 ^ (prefixWord ++ tailWord_4063128).sum := by decide
  have hdescent : baseEnd_4063128 < baseStart_4063128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063167 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 2, 5, 2]
def baseStart_4063167 : Nat := 118140960795 + 4063167 * 2 ^ 59
def prefixEnd_4063167 : Nat := 4983230072969 + 3 ^ 40 * 4063167 * 2
def baseEnd_4063167 : Nat := 2086357650487009574126341

theorem tailTrace_4063167 : CollatzResearch.WordTrace tailWord_4063167 prefixEnd_4063167 2086357650487009574126341 := by
  unfold tailWord_4063167
  simp only [CollatzResearch.WordTrace]
  refine ⟨148195875270847367521827755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98797250180564911681218503 148195875270847367521827755)
  ·
    refine ⟨222293812906271051282741633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148195875270847367521827755 222293812906271051282741633)
    ·
      refine ⟨166720359679703288462056225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222293812906271051282741633 166720359679703288462056225)
      ·
        refine ⟨125040269759777466346542169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166720359679703288462056225 125040269759777466346542169)
        ·
          refine ⟨93780202319833099759906627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125040269759777466346542169 93780202319833099759906627)
          ·
            refine ⟨140670303479749649639859941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93780202319833099759906627 140670303479749649639859941)
            ·
              refine ⟨26375681902453059307473739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140670303479749649639859941 26375681902453059307473739)
              ·
                refine ⟨39563522853679588961210609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26375681902453059307473739 39563522853679588961210609)
                ·
                  refine ⟨29672642140259691720907957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39563522853679588961210609 29672642140259691720907957)
                  ·
                    refine ⟨2781810200649346098835121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29672642140259691720907957 2781810200649346098835121)
                    ·
                      refine ⟨2086357650487009574126341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781810200649346098835121 2086357650487009574126341)
                      ·
                        rfl

theorem cell23_4063167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_4063167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063167 prefixEnd_4063167 := by exact prefixLift 4063167
  have htrace : WordTrace (prefixWord ++ tailWord_4063167) baseStart_4063167 baseEnd_4063167 := by
    simpa [prefixWord, tailWord_4063167, baseEnd_4063167] using wordTrace_append hprefix tailTrace_4063167
  have hstable : (prefixWord ++ tailWord_4063167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063167).length < 2 ^ (prefixWord ++ tailWord_4063167).sum := by decide
  have hdescent : baseEnd_4063167 < baseStart_4063167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063194 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_4063194 : Nat := 118140960795 + 4063194 * 2 ^ 59
def prefixEnd_4063194 : Nat := 4983230072969 + 3 ^ 40 * 4063194 * 2
def baseEnd_4063194 : Nat := 695457171488226989496239

theorem tailTrace_4063194 : CollatzResearch.WordTrace tailWord_4063194 prefixEnd_4063194 695457171488226989496239 := by
  unfold tailWord_4063194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37049215010437387783265159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98797906694499700755373757 37049215010437387783265159)
  ·
    refine ⟨55573822515656081674897739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37049215010437387783265159 55573822515656081674897739)
    ·
      refine ⟨83360733773484122512346609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55573822515656081674897739 83360733773484122512346609)
      ·
        refine ⟨62520550330113091884259957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83360733773484122512346609 62520550330113091884259957)
        ·
          refine ⟨5861301593448102364149371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62520550330113091884259957 5861301593448102364149371)
          ·
            refine ⟨8791952390172153546224057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861301593448102364149371 8791952390172153546224057)
            ·
              refine ⟨6593964292629115159668043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8791952390172153546224057 6593964292629115159668043)
              ·
                refine ⟨9890946438943672739502065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593964292629115159668043 9890946438943672739502065)
                ·
                  refine ⟨7418209829207754554626549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9890946438943672739502065 7418209829207754554626549)
                  ·
                    refine ⟨695457171488226989496239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7418209829207754554626549 695457171488226989496239)
                    ·
                      rfl

theorem cell23_4063194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_4063194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063194 prefixEnd_4063194 := by exact prefixLift 4063194
  have htrace : WordTrace (prefixWord ++ tailWord_4063194) baseStart_4063194 baseEnd_4063194 := by
    simpa [prefixWord, tailWord_4063194, baseEnd_4063194] using wordTrace_append hprefix tailTrace_4063194
  have hstable : (prefixWord ++ tailWord_4063194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063194).length < 2 ^ (prefixWord ++ tailWord_4063194).sum := by decide
  have hdescent : baseEnd_4063194 < baseStart_4063194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063214 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_4063214 : Nat := 118140960795 + 4063214 * 2 ^ 59
def prefixEnd_4063214 : Nat := 4983230072969 + 3 ^ 40 * 4063214 * 2
def baseEnd_4063214 : Nat := 2086381784077770890238625

theorem tailTrace_4063214 : CollatzResearch.WordTrace tailWord_4063214 prefixEnd_4063214 2086381784077770890238625 := by
  unfold tailWord_4063214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18524698687709636818598587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98798393001118063032525797 18524698687709636818598587)
  ·
    refine ⟨27787048031564455227897881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18524698687709636818598587 27787048031564455227897881)
    ·
      refine ⟨20840286023673341420923411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27787048031564455227897881 20840286023673341420923411)
      ·
        refine ⟨31260429035510012131385117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20840286023673341420923411 31260429035510012131385117)
        ·
          refine ⟨11722660888316254549269419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31260429035510012131385117 11722660888316254549269419)
          ·
            refine ⟨17583991332474381823904129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722660888316254549269419 17583991332474381823904129)
            ·
              refine ⟨13187993499355786367928097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17583991332474381823904129 13187993499355786367928097)
              ·
                refine ⟨9890995124516839775946073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13187993499355786367928097 9890995124516839775946073)
                ·
                  refine ⟨7418246343387629831959555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9890995124516839775946073 7418246343387629831959555)
                  ·
                    refine ⟨11127369515081444747939333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7418246343387629831959555 11127369515081444747939333)
                    ·
                      refine ⟨2086381784077770890238625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11127369515081444747939333 2086381784077770890238625)
                      ·
                        rfl

theorem cell23_4063214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_4063214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063214 prefixEnd_4063214 := by exact prefixLift 4063214
  have htrace : WordTrace (prefixWord ++ tailWord_4063214) baseStart_4063214 baseEnd_4063214 := by
    simpa [prefixWord, tailWord_4063214, baseEnd_4063214] using wordTrace_append hprefix tailTrace_4063214
  have hstable : (prefixWord ++ tailWord_4063214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063214).length < 2 ^ (prefixWord ++ tailWord_4063214).sum := by decide
  have hdescent : baseEnd_4063214 < baseStart_4063214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063237 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 6]
def baseStart_4063237 : Nat := 118140960795 + 4063237 * 2 ^ 59
def prefixEnd_4063237 : Nat := 4983230072969 + 3 ^ 40 * 4063237 * 2
def baseEnd_4063237 : Nat := 231821510459202700027891

theorem tailTrace_4063237 : CollatzResearch.WordTrace tailWord_4063237 prefixEnd_4063237 231821510459202700027891 := by
  unfold tailWord_4063237
  simp only [CollatzResearch.WordTrace]
  refine ⟨148198428380593769476875965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98798952253729179651250643 148198428380593769476875965)
  ·
    refine ⟨55574410642722663553828487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148198428380593769476875965 55574410642722663553828487)
    ·
      refine ⟨83361615964083995330742731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55574410642722663553828487 83361615964083995330742731)
      ·
        refine ⟨125042423946125992996114097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83361615964083995330742731 125042423946125992996114097)
        ·
          refine ⟨93781817959594494747085573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125042423946125992996114097 93781817959594494747085573)
          ·
            refine ⟨17584090867423967765078545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93781817959594494747085573 17584090867423967765078545)
            ·
              refine ⟨13188068150567975823808909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17584090867423967765078545 13188068150567975823808909)
              ·
                refine ⟨4945525556462990933928341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13188068150567975823808909 4945525556462990933928341)
                ·
                  refine ⟨231821510459202700027891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4945525556462990933928341 231821510459202700027891)
                  ·
                    rfl

theorem cell23_4063237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_4063237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063237 prefixEnd_4063237 := by exact prefixLift 4063237
  have htrace : WordTrace (prefixWord ++ tailWord_4063237) baseStart_4063237 baseEnd_4063237 := by
    simpa [prefixWord, tailWord_4063237, baseEnd_4063237] using wordTrace_append hprefix tailTrace_4063237
  have hstable : (prefixWord ++ tailWord_4063237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063237).length < 2 ^ (prefixWord ++ tailWord_4063237).sum := by decide
  have hdescent : baseEnd_4063237 < baseStart_4063237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063245 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_4063245 : Nat := 118140960795 + 4063245 * 2 ^ 59
def prefixEnd_4063245 : Nat := 4983230072969 + 3 ^ 40 * 4063245 * 2
def baseEnd_4063245 : Nat := 695465900659353422983661

theorem tailTrace_4063245 : CollatzResearch.WordTrace tailWord_4063245 prefixEnd_4063245 695465900659353422983661 := by
  unfold tailWord_4063245
  simp only [CollatzResearch.WordTrace]
  refine ⟨148198720164564786843167189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98799146776376524562111459 148198720164564786843167189)
  ·
    refine ⟨3473407503856987191636731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 148198720164564786843167189 3473407503856987191636731)
    ·
      refine ⟨5210111255785480787455097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3473407503856987191636731 5210111255785480787455097)
      ·
        refine ⟨3907583441839110590591323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5210111255785480787455097 3907583441839110590591323)
        ·
          refine ⟨5861375162758665885886985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907583441839110590591323 5861375162758665885886985)
          ·
            refine ⟨4396031372068999414415239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5861375162758665885886985 4396031372068999414415239)
            ·
              refine ⟨6594047058103499121622859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396031372068999414415239 6594047058103499121622859)
              ·
                refine ⟨9891070587155248682434289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594047058103499121622859 9891070587155248682434289)
                ·
                  refine ⟨7418302940366436511825717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9891070587155248682434289 7418302940366436511825717)
                  ·
                    refine ⟨695465900659353422983661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7418302940366436511825717 695465900659353422983661)
                    ·
                      rfl

theorem cell23_4063245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_4063245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063245 prefixEnd_4063245 := by exact prefixLift 4063245
  have htrace : WordTrace (prefixWord ++ tailWord_4063245) baseStart_4063245 baseEnd_4063245 := by
    simpa [prefixWord, tailWord_4063245, baseEnd_4063245] using wordTrace_append hprefix tailTrace_4063245
  have hstable : (prefixWord ++ tailWord_4063245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063245).length < 2 ^ (prefixWord ++ tailWord_4063245).sum := by decide
  have hdescent : baseEnd_4063245 < baseStart_4063245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063281 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 3]
def baseStart_4063281 : Nat := 118140960795 + 4063281 * 2 ^ 59
def prefixEnd_4063281 : Nat := 4983230072969 + 3 ^ 40 * 4063281 * 2
def baseEnd_4063281 : Nat := 2086416187281622128100817

theorem tailTrace_4063281 : CollatzResearch.WordTrace tailWord_4063281 prefixEnd_4063281 2086416187281622128100817 := by
  unfold tailWord_4063281
  simp only [CollatzResearch.WordTrace]
  refine ⟨148200033192434364991477697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98800022128289576660985131 148200033192434364991477697)
  ·
    refine ⟨111150024894325773743608273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148200033192434364991477697 111150024894325773743608273)
    ·
      refine ⟨83362518670744330307706205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111150024894325773743608273 83362518670744330307706205)
      ·
        refine ⟨31260944501529123865389827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83362518670744330307706205 31260944501529123865389827)
        ·
          refine ⟨46891416752293685798084741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31260944501529123865389827 46891416752293685798084741)
          ·
            refine ⟨8792140641055066087140889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46891416752293685798084741 8792140641055066087140889)
            ·
              refine ⟨6594105480791299565355667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8792140641055066087140889 6594105480791299565355667)
              ·
                refine ⟨9891158221186949348033501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594105480791299565355667 9891158221186949348033501)
                ·
                  refine ⟨3709184332945106005512563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9891158221186949348033501 3709184332945106005512563)
                  ·
                    refine ⟨5563776499417659008268845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3709184332945106005512563 5563776499417659008268845)
                    ·
                      refine ⟨2086416187281622128100817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5563776499417659008268845 2086416187281622128100817)
                      ·
                        rfl

theorem cell23_4063281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_4063281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063281 prefixEnd_4063281 := by exact prefixLift 4063281
  have htrace : WordTrace (prefixWord ++ tailWord_4063281) baseStart_4063281 baseEnd_4063281 := by
    simpa [prefixWord, tailWord_4063281, baseEnd_4063281] using wordTrace_append hprefix tailTrace_4063281
  have hstable : (prefixWord ++ tailWord_4063281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063281).length < 2 ^ (prefixWord ++ tailWord_4063281).sum := by decide
  have hdescent : baseEnd_4063281 < baseStart_4063281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063287 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_4063287 : Nat := 118140960795 + 4063287 * 2 ^ 59
def prefixEnd_4063287 : Nat := 4983230072969 + 3 ^ 40 * 4063287 * 2
def baseEnd_4063287 : Nat := 2086419268165549104625789

theorem tailTrace_4063287 : CollatzResearch.WordTrace tailWord_4063287 prefixEnd_4063287 2086419268165549104625789 := by
  unfold tailWord_4063287
  simp only [CollatzResearch.WordTrace]
  refine ⟨148200252030412628016196115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98800168020275085344130743 148200252030412628016196115)
  ·
    refine ⟨222300378045618942024294173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148200252030412628016196115 222300378045618942024294173)
    ·
      refine ⟨83362641767107103259110315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222300378045618942024294173 83362641767107103259110315)
      ·
        refine ⟨125043962650660654888665473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83362641767107103259110315 125043962650660654888665473)
        ·
          refine ⟨93782971987995491166499105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125043962650660654888665473 93782971987995491166499105)
          ·
            refine ⟨70337228990996618374874329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93782971987995491166499105 70337228990996618374874329)
            ·
              refine ⟨52752921743247463781155747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70337228990996618374874329 52752921743247463781155747)
              ·
                refine ⟨79129382614871195671733621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52752921743247463781155747 79129382614871195671733621)
                ·
                  refine ⟨7418379620144174594225027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79129382614871195671733621 7418379620144174594225027)
                  ·
                    refine ⟨11127569430216261891337541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7418379620144174594225027 11127569430216261891337541)
                    ·
                      refine ⟨2086419268165549104625789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11127569430216261891337541 2086419268165549104625789)
                      ·
                        rfl

theorem cell23_4063287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_4063287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063287 prefixEnd_4063287 := by exact prefixLift 4063287
  have htrace : WordTrace (prefixWord ++ tailWord_4063287) baseStart_4063287 baseEnd_4063287 := by
    simpa [prefixWord, tailWord_4063287, baseEnd_4063287] using wordTrace_append hprefix tailTrace_4063287
  have hstable : (prefixWord ++ tailWord_4063287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063287).length < 2 ^ (prefixWord ++ tailWord_4063287).sum := by decide
  have hdescent : baseEnd_4063287 < baseStart_4063287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063318 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4063318 : Nat := 118140960795 + 4063318 * 2 ^ 59
def prefixEnd_4063318 : Nat := 4983230072969 + 3 ^ 40 * 4063318 * 2
def baseEnd_4063318 : Nat := 695478395355279494446049

theorem tailTrace_4063318 : CollatzResearch.WordTrace tailWord_4063318 prefixEnd_4063318 695478395355279494446049 := by
  unfold tailWord_4063318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262586418331270019410913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98800921795533546873716405 9262586418331270019410913)
  ·
    refine ⟨6946939813748452514558185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9262586418331270019410913 6946939813748452514558185)
    ·
      refine ⟨5210204860311339385918639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6946939813748452514558185 5210204860311339385918639)
      ·
        refine ⟨7815307290467009078877959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210204860311339385918639 7815307290467009078877959)
        ·
          refine ⟨11722960935700513618316939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815307290467009078877959 11722960935700513618316939)
          ·
            refine ⟨17584441403550770427475409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722960935700513618316939 17584441403550770427475409)
            ·
              refine ⟨13188331052663077820606557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17584441403550770427475409 13188331052663077820606557)
              ·
                refine ⟨4945624144748654182727459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13188331052663077820606557 4945624144748654182727459)
                ·
                  refine ⟨7418436217122981274091189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945624144748654182727459 7418436217122981274091189)
                  ·
                    refine ⟨695478395355279494446049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7418436217122981274091189 695478395355279494446049)
                    ·
                      rfl

theorem cell23_4063318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4063318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063318 prefixEnd_4063318 := by exact prefixLift 4063318
  have htrace : WordTrace (prefixWord ++ tailWord_4063318) baseStart_4063318 baseEnd_4063318 := by
    simpa [prefixWord, tailWord_4063318, baseEnd_4063318] using wordTrace_append hprefix tailTrace_4063318
  have hstable : (prefixWord ++ tailWord_4063318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063318).length < 2 ^ (prefixWord ++ tailWord_4063318).sum := by decide
  have hdescent : baseEnd_4063318 < baseStart_4063318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063324 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_4063324 : Nat := 118140960795 + 4063324 * 2 ^ 59
def prefixEnd_4063324 : Nat := 4983230072969 + 3 ^ 40 * 4063324 * 2
def baseEnd_4063324 : Nat := 2086438266949765459863119

theorem tailTrace_4063324 : CollatzResearch.WordTrace tailWord_4063324 prefixEnd_4063324 2086438266949765459863119 := by
  unfold tailWord_4063324
  simp only [CollatzResearch.WordTrace]
  refine ⟨74100800765639291667646513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98801067687519055556862017 74100800765639291667646513)
  ·
    refine ⟨55575600574229468750734885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74100800765639291667646513 55575600574229468750734885)
    ·
      refine ⟨10420425107668025390762791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55575600574229468750734885 10420425107668025390762791)
      ·
        refine ⟨15630637661502038086144187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10420425107668025390762791 15630637661502038086144187)
        ·
          refine ⟨23445956492253057129216281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15630637661502038086144187 23445956492253057129216281)
          ·
            refine ⟨17584467369189792846912211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23445956492253057129216281 17584467369189792846912211)
            ·
              refine ⟨26376701053784689270368317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17584467369189792846912211 26376701053784689270368317)
              ·
                refine ⟨9891262895169258476388119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26376701053784689270368317 9891262895169258476388119)
                ·
                  refine ⟨14836894342753887714582179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9891262895169258476388119 14836894342753887714582179)
                  ·
                    refine ⟨22255341514130831571873269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14836894342753887714582179 22255341514130831571873269)
                    ·
                      refine ⟨2086438266949765459863119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22255341514130831571873269 2086438266949765459863119)
                      ·
                        rfl

theorem cell23_4063324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_4063324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063324 prefixEnd_4063324 := by exact prefixLift 4063324
  have htrace : WordTrace (prefixWord ++ tailWord_4063324) baseStart_4063324 baseEnd_4063324 := by
    simpa [prefixWord, tailWord_4063324, baseEnd_4063324] using wordTrace_append hprefix tailTrace_4063324
  have hstable : (prefixWord ++ tailWord_4063324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063324).length < 2 ^ (prefixWord ++ tailWord_4063324).sum := by decide
  have hdescent : baseEnd_4063324 < baseStart_4063324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063367 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_4063367 : Nat := 118140960795 + 4063367 * 2 ^ 59
def prefixEnd_4063367 : Nat := 4983230072969 + 3 ^ 40 * 4063367 * 2
def baseEnd_4063367 : Nat := 2086460346617908791625421

theorem tailTrace_4063367 : CollatzResearch.WordTrace tailWord_4063367 prefixEnd_4063367 2086460346617908791625421 := by
  unfold tailWord_4063367
  simp only [CollatzResearch.WordTrace]
  refine ⟨148203169870122801679108355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98802113246748534452738903 148203169870122801679108355)
  ·
    refine ⟨222304754805184202518662533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148203169870122801679108355 222304754805184202518662533)
    ·
      refine ⟨41682141525972037972249225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222304754805184202518662533 41682141525972037972249225)
      ·
        refine ⟨31261606144479028479186919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41682141525972037972249225 31261606144479028479186919)
        ·
          refine ⟨46892409216718542718780379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31261606144479028479186919 46892409216718542718780379)
          ·
            refine ⟨70338613825077814078170569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46892409216718542718780379 70338613825077814078170569)
            ·
              refine ⟨52753960368808360558627927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70338613825077814078170569 52753960368808360558627927)
              ·
                refine ⟨79130940553212540837941891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52753960368808360558627927 79130940553212540837941891)
                ·
                  refine ⟨118696410829818811256912837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79130940553212540837941891 118696410829818811256912837)
                  ·
                    refine ⟨22255577030591027110671157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118696410829818811256912837 22255577030591027110671157)
                    ·
                      refine ⟨2086460346617908791625421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22255577030591027110671157 2086460346617908791625421)
                      ·
                        rfl

theorem cell23_4063367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_4063367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063367 prefixEnd_4063367 := by exact prefixLift 4063367
  have htrace : WordTrace (prefixWord ++ tailWord_4063367) baseStart_4063367 baseEnd_4063367 := by
    simpa [prefixWord, tailWord_4063367, baseEnd_4063367] using wordTrace_append hprefix tailTrace_4063367
  have hstable : (prefixWord ++ tailWord_4063367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063367).length < 2 ^ (prefixWord ++ tailWord_4063367).sum := by decide
  have hdescent : baseEnd_4063367 < baseStart_4063367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063377 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_4063377 : Nat := 118140960795 + 4063377 * 2 ^ 59
def prefixEnd_4063377 : Nat := 4983230072969 + 3 ^ 40 * 4063377 * 2
def baseEnd_4063377 : Nat := 2086465481424453752500375

theorem tailTrace_4063377 : CollatzResearch.WordTrace tailWord_4063377 prefixEnd_4063377 2086465481424453752500375 := by
  unfold tailWord_4063377
  simp only [CollatzResearch.WordTrace]
  refine ⟨148203534600086573386972385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98802356400057715591314923 148203534600086573386972385)
  ·
    refine ⟨111152650950064930040229289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148203534600086573386972385 111152650950064930040229289)
    ·
      refine ⟨83364488212548697530171967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111152650950064930040229289 83364488212548697530171967)
      ·
        refine ⟨125046732318823046295257951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83364488212548697530171967 125046732318823046295257951)
        ·
          refine ⟨187570098478234569442886927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125046732318823046295257951 187570098478234569442886927)
          ·
            refine ⟨281355147717351854164330391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187570098478234569442886927 281355147717351854164330391)
            ·
              refine ⟨422032721576027781246495587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281355147717351854164330391 422032721576027781246495587)
              ·
                refine ⟨633049082364041671869743381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422032721576027781246495587 633049082364041671869743381)
                ·
                  refine ⟨29674175735814453368894221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 633049082364041671869743381 29674175735814453368894221)
                  ·
                    refine ⟨11127815900930420013335333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29674175735814453368894221 11127815900930420013335333)
                    ·
                      refine ⟨2086465481424453752500375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11127815900930420013335333 2086465481424453752500375)
                      ·
                        rfl

theorem cell23_4063377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_4063377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063377 prefixEnd_4063377 := by exact prefixLift 4063377
  have htrace : WordTrace (prefixWord ++ tailWord_4063377) baseStart_4063377 baseEnd_4063377 := by
    simpa [prefixWord, tailWord_4063377, baseEnd_4063377] using wordTrace_append hprefix tailTrace_4063377
  have hstable : (prefixWord ++ tailWord_4063377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063377).length < 2 ^ (prefixWord ++ tailWord_4063377).sum := by decide
  have hdescent : baseEnd_4063377 < baseStart_4063377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063388 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_4063388 : Nat := 118140960795 + 4063388 * 2 ^ 59
def prefixEnd_4063388 : Nat := 4983230072969 + 3 ^ 40 * 4063388 * 2
def baseEnd_4063388 : Nat := 2086471129711653209462825

theorem tailTrace_4063388 : CollatzResearch.WordTrace tailWord_4063388 prefixEnd_4063388 2086471129711653209462825 := by
  unfold tailWord_4063388
  simp only [CollatzResearch.WordTrace]
  refine ⟨74101967901523361132811409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98802623868697814843748545 74101967901523361132811409)
  ·
    refine ⟨55576475926142520849608557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74101967901523361132811409 55576475926142520849608557)
    ·
      refine ⟨20841178472303445318603209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55576475926142520849608557 20841178472303445318603209)
      ·
        refine ⟨15630883854227583988952407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20841178472303445318603209 15630883854227583988952407)
        ·
          refine ⟨23446325781341375983428611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15630883854227583988952407 23446325781341375983428611)
          ·
            refine ⟨35169488672012063975142917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23446325781341375983428611 35169488672012063975142917)
            ·
              refine ⟨6594279126002261995339297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35169488672012063975142917 6594279126002261995339297)
              ·
                refine ⟨4945709344501696496504473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6594279126002261995339297 4945709344501696496504473)
                ·
                  refine ⟨3709282008376272372378355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4945709344501696496504473 3709282008376272372378355)
                  ·
                    refine ⟨5563923012564408558567533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3709282008376272372378355 5563923012564408558567533)
                    ·
                      refine ⟨2086471129711653209462825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5563923012564408558567533 2086471129711653209462825)
                      ·
                        rfl

theorem cell23_4063388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_4063388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063388 prefixEnd_4063388 := by exact prefixLift 4063388
  have htrace : WordTrace (prefixWord ++ tailWord_4063388) baseStart_4063388 baseEnd_4063388 := by
    simpa [prefixWord, tailWord_4063388, baseEnd_4063388] using wordTrace_append hprefix tailTrace_4063388
  have hstable : (prefixWord ++ tailWord_4063388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063388).length < 2 ^ (prefixWord ++ tailWord_4063388).sum := by decide
  have hdescent : baseEnd_4063388 < baseStart_4063388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063411 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 6, 2, 2]
def baseStart_4063411 : Nat := 118140960795 + 4063411 * 2 ^ 59
def prefixEnd_4063411 : Nat := 4983230072969 + 3 ^ 40 * 4063411 * 2
def baseEnd_4063411 : Nat := 2086482939766706619475219

theorem tailTrace_4063411 : CollatzResearch.WordTrace tailWord_4063411 prefixEnd_4063411 2086482939766706619475219 := by
  unfold tailWord_4063411
  simp only [CollatzResearch.WordTrace]
  refine ⟨148204774681963397193710087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98803183121308931462473391 148204774681963397193710087)
  ·
    refine ⟨222307162022945095790565131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148204774681963397193710087 222307162022945095790565131)
    ·
      refine ⟨333460743034417643685847697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222307162022945095790565131 333460743034417643685847697)
      ·
        refine ⟨250095557275813232764385773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333460743034417643685847697 250095557275813232764385773)
        ·
          refine ⟨93785833978429962286644665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250095557275813232764385773 93785833978429962286644665)
          ·
            refine ⟨70339375483822471714983499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93785833978429962286644665 70339375483822471714983499)
            ·
              refine ⟨105509063225733707572475249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70339375483822471714983499 105509063225733707572475249)
              ·
                refine ⟨79131797419300280679356437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105509063225733707572475249 79131797419300280679356437)
                ·
                  refine ⟨3709303004029700656844833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79131797419300280679356437 3709303004029700656844833)
                  ·
                    refine ⟨2781977253022275492633625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3709303004029700656844833 2781977253022275492633625)
                    ·
                      refine ⟨2086482939766706619475219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781977253022275492633625 2086482939766706619475219)
                      ·
                        rfl

theorem cell23_4063411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 2, 2].length) (baseStart_4063411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063411 prefixEnd_4063411 := by exact prefixLift 4063411
  have htrace : WordTrace (prefixWord ++ tailWord_4063411) baseStart_4063411 baseEnd_4063411 := by
    simpa [prefixWord, tailWord_4063411, baseEnd_4063411] using wordTrace_append hprefix tailTrace_4063411
  have hstable : (prefixWord ++ tailWord_4063411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063411).length < 2 ^ (prefixWord ++ tailWord_4063411).sum := by decide
  have hdescent : baseEnd_4063411 < baseStart_4063411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063428 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_4063428 : Nat := 118140960795 + 4063428 * 2 ^ 59
def prefixEnd_4063428 : Nat := 4983230072969 + 3 ^ 40 * 4063428 * 2
def baseEnd_4063428 : Nat := 2086491668937833052962641

theorem tailTrace_4063428 : CollatzResearch.WordTrace tailWord_4063428 prefixEnd_4063428 2086491668937833052962641 := by
  unfold tailWord_4063428
  simp only [CollatzResearch.WordTrace]
  refine ⟨74102697361450904548539469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98803596481934539398052625 74102697361450904548539469)
  ·
    refine ⟨27788511510544089205702301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74102697361450904548539469 27788511510544089205702301)
    ·
      refine ⟨10420691816454033452138363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27788511510544089205702301 10420691816454033452138363)
      ·
        refine ⟨15631037724681050178207545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10420691816454033452138363 15631037724681050178207545)
        ·
          refine ⟨11723278293510787633655659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15631037724681050178207545 11723278293510787633655659)
          ·
            refine ⟨17584917440266181450483489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11723278293510787633655659 17584917440266181450483489)
            ·
              refine ⟨13188688080199636087862617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17584917440266181450483489 13188688080199636087862617)
              ·
                refine ⟨9891516060149727065896963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13188688080199636087862617 9891516060149727065896963)
                ·
                  refine ⟨14837274090224590598845445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9891516060149727065896963 14837274090224590598845445)
                  ·
                    refine ⟨2781988891917110737283521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14837274090224590598845445 2781988891917110737283521)
                    ·
                      refine ⟨2086491668937833052962641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2781988891917110737283521 2086491668937833052962641)
                      ·
                        rfl

theorem cell23_4063428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_4063428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063428 prefixEnd_4063428 := by exact prefixLift 4063428
  have htrace : WordTrace (prefixWord ++ tailWord_4063428) baseStart_4063428 baseEnd_4063428 := by
    simpa [prefixWord, tailWord_4063428, baseEnd_4063428] using wordTrace_append hprefix tailTrace_4063428
  have hstable : (prefixWord ++ tailWord_4063428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063428).length < 2 ^ (prefixWord ++ tailWord_4063428).sum := by decide
  have hdescent : baseEnd_4063428 < baseStart_4063428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063445 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_4063445 : Nat := 118140960795 + 4063445 * 2 ^ 59
def prefixEnd_4063445 : Nat := 4983230072969 + 3 ^ 40 * 4063445 * 2
def baseEnd_4063445 : Nat := 2086500398108959486450063

theorem tailTrace_4063445 : CollatzResearch.WordTrace tailWord_4063445 prefixEnd_4063445 2086500398108959486450063 := by
  unfold tailWord_4063445
  simp only [CollatzResearch.WordTrace]
  refine ⟨148206014763840221000447789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98804009842560147333631859 148206014763840221000447789)
  ·
    refine ⟨55577255536440082875167921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148206014763840221000447789 55577255536440082875167921)
    ·
      refine ⟨41682941652330062156375941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55577255536440082875167921 41682941652330062156375941)
      ·
        refine ⟨7815551559811886654320489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41682941652330062156375941 7815551559811886654320489)
        ·
          refine ⟨5861663669858914990740367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7815551559811886654320489 5861663669858914990740367)
          ·
            refine ⟨8792495504788372486110551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861663669858914990740367 8792495504788372486110551)
            ·
              refine ⟨13188743257182558729165827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792495504788372486110551 13188743257182558729165827)
              ·
                refine ⟨19783114885773838093748741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188743257182558729165827 19783114885773838093748741)
                ·
                  refine ⟨3709334041082594642577889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19783114885773838093748741 3709334041082594642577889)
                  ·
                    refine ⟨2782000530811945981933417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3709334041082594642577889 2782000530811945981933417)
                    ·
                      refine ⟨2086500398108959486450063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782000530811945981933417 2086500398108959486450063)
                      ·
                        rfl

theorem cell23_4063445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_4063445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063445 prefixEnd_4063445 := by exact prefixLift 4063445
  have htrace : WordTrace (prefixWord ++ tailWord_4063445) baseStart_4063445 baseEnd_4063445 := by
    simpa [prefixWord, tailWord_4063445, baseEnd_4063445] using wordTrace_append hprefix tailTrace_4063445
  have hstable : (prefixWord ++ tailWord_4063445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063445).length < 2 ^ (prefixWord ++ tailWord_4063445).sum := by decide
  have hdescent : baseEnd_4063445 < baseStart_4063445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063461 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_4063461 : Nat := 118140960795 + 4063461 * 2 ^ 59
def prefixEnd_4063461 : Nat := 4983230072969 + 3 ^ 40 * 4063461 * 2
def baseEnd_4063461 : Nat := 2086508613799431423849989

theorem tailTrace_4063461 : CollatzResearch.WordTrace tailWord_4063461 prefixEnd_4063461 2086508613799431423849989 := by
  unfold tailWord_4063461
  simp only [CollatzResearch.WordTrace]
  refine ⟨148206598331782255733030237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98804398887854837155353491 148206598331782255733030237)
  ·
    refine ⟨55577474374418345899886339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148206598331782255733030237 55577474374418345899886339)
    ·
      refine ⟨83366211561627518849829509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55577474374418345899886339 83366211561627518849829509)
      ·
        refine ⟨15631164667805159784343033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83366211561627518849829509 15631164667805159784343033)
        ·
          refine ⟨11723373500853869838257275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15631164667805159784343033 11723373500853869838257275)
          ·
            refine ⟨17585060251280804757385913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11723373500853869838257275 17585060251280804757385913)
            ·
              refine ⟨13188795188460603568039435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17585060251280804757385913 13188795188460603568039435)
              ·
                refine ⟨19783192782690905352059153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188795188460603568039435 19783192782690905352059153)
                ·
                  refine ⟨14837394587018179014044365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19783192782690905352059153 14837394587018179014044365)
                  ·
                    refine ⟨5564022970131817130266637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14837394587018179014044365 5564022970131817130266637)
                    ·
                      refine ⟨2086508613799431423849989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5564022970131817130266637 2086508613799431423849989)
                      ·
                        rfl

theorem cell23_4063461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_4063461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063461 prefixEnd_4063461 := by exact prefixLift 4063461
  have htrace : WordTrace (prefixWord ++ tailWord_4063461) baseStart_4063461 baseEnd_4063461 := by
    simpa [prefixWord, tailWord_4063461, baseEnd_4063461] using wordTrace_append hprefix tailTrace_4063461
  have hstable : (prefixWord ++ tailWord_4063461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063461).length < 2 ^ (prefixWord ++ tailWord_4063461).sum := by decide
  have hdescent : baseEnd_4063461 < baseStart_4063461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063464 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 1, 7]
def baseStart_4063464 : Nat := 118140960795 + 4063464 * 2 ^ 59
def prefixEnd_4063464 : Nat := 4983230072969 + 3 ^ 40 * 4063464 * 2
def baseEnd_4063464 : Nat := 695503384747131637370825

theorem tailTrace_4063464 : CollatzResearch.WordTrace tailWord_4063464 prefixEnd_4063464 695503384747131637370825 := by
  unfold tailWord_4063464
  simp only [CollatzResearch.WordTrace]
  refine ⟨74103353875385693622694723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98804471833847591496926297 74103353875385693622694723)
  ·
    refine ⟨111155030813078540434042085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74103353875385693622694723 111155030813078540434042085)
    ·
      refine ⟨20841568277452226331382891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111155030813078540434042085 20841568277452226331382891)
      ·
        refine ⟨31262352416178339497074337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20841568277452226331382891 31262352416178339497074337)
        ·
          refine ⟨23446764312133754622805753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31262352416178339497074337 23446764312133754622805753)
          ·
            refine ⟨17585073234100315967104315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23446764312133754622805753 17585073234100315967104315)
            ·
              refine ⟨26377609851150473950656473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17585073234100315967104315 26377609851150473950656473)
              ·
                refine ⟨19783207388362855462992355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26377609851150473950656473 19783207388362855462992355)
                ·
                  refine ⟨29674811082544283194488533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19783207388362855462992355 29674811082544283194488533)
                  ·
                    refine ⟨695503384747131637370825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29674811082544283194488533 695503384747131637370825)
                    ·
                      rfl

theorem cell23_4063464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_4063464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063464 prefixEnd_4063464 := by exact prefixLift 4063464
  have htrace : WordTrace (prefixWord ++ tailWord_4063464) baseStart_4063464 baseEnd_4063464 := by
    simpa [prefixWord, tailWord_4063464, baseEnd_4063464] using wordTrace_append hprefix tailTrace_4063464
  have hstable : (prefixWord ++ tailWord_4063464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063464).length < 2 ^ (prefixWord ++ tailWord_4063464).sum := by decide
  have hdescent : baseEnd_4063464 < baseStart_4063464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063561 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 3, 5, 2]
def baseStart_4063561 : Nat := 118140960795 + 4063561 * 2 ^ 59
def prefixEnd_4063561 : Nat := 4983230072969 + 3 ^ 40 * 4063561 * 2
def baseEnd_4063561 : Nat := 2086559961864881032599529

theorem tailTrace_4063561 : CollatzResearch.WordTrace tailWord_4063561 prefixEnd_4063561 2086559961864881032599529 := by
  unfold tailWord_4063561
  simp only [CollatzResearch.WordTrace]
  refine ⟨148210245631419972811670537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98806830420946648541113691 148210245631419972811670537)
  ·
    refine ⟨111157684223564979608752903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148210245631419972811670537 111157684223564979608752903)
    ·
      refine ⟨166736526335347469413129355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111157684223564979608752903 166736526335347469413129355)
      ·
        refine ⟨250104789503021204119694033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166736526335347469413129355 250104789503021204119694033)
        ·
          refine ⟨187578592127265903089770525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250104789503021204119694033 187578592127265903089770525)
          ·
            refine ⟨70341972047724713658663947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187578592127265903089770525 70341972047724713658663947)
            ·
              refine ⟨105512958071587070487995921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70341972047724713658663947 105512958071587070487995921)
              ·
                refine ⟨79134718553690302865996941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105512958071587070487995921 79134718553690302865996941)
                ·
                  refine ⟨29675519457633863574748853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79134718553690302865996941 29675519457633863574748853)
                  ·
                    refine ⟨2782079949153174710132705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29675519457633863574748853 2782079949153174710132705)
                    ·
                      refine ⟨2086559961864881032599529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782079949153174710132705 2086559961864881032599529)
                      ·
                        rfl

theorem cell23_4063561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 5, 2].length) (baseStart_4063561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063561 prefixEnd_4063561 := by exact prefixLift 4063561
  have htrace : WordTrace (prefixWord ++ tailWord_4063561) baseStart_4063561 baseEnd_4063561 := by
    simpa [prefixWord, tailWord_4063561, baseEnd_4063561] using wordTrace_append hprefix tailTrace_4063561
  have hstable : (prefixWord ++ tailWord_4063561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063561).length < 2 ^ (prefixWord ++ tailWord_4063561).sum := by decide
  have hdescent : baseEnd_4063561 < baseStart_4063561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063601 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 4, 4]
def baseStart_4063601 : Nat := 118140960795 + 4063601 * 2 ^ 59
def prefixEnd_4063601 : Nat := 4983230072969 + 3 ^ 40 * 4063601 * 2
def baseEnd_4063601 : Nat := 695526833697020292033115

theorem tailTrace_4063601 : CollatzResearch.WordTrace tailWord_4063601 prefixEnd_4063601 695526833697020292033115 := by
  unfold tailWord_4063601
  simp only [CollatzResearch.WordTrace]
  refine ⟨148211704551275059643126657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98807803034183373095417771 148211704551275059643126657)
  ·
    refine ⟨111158778413456294732344993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148211704551275059643126657 111158778413456294732344993)
    ·
      refine ⟨83369083810092221049258745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111158778413456294732344993 83369083810092221049258745)
      ·
        refine ⟨62526812857569165786944059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83369083810092221049258745 62526812857569165786944059)
        ·
          refine ⟨93790219286353748680416089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62526812857569165786944059 93790219286353748680416089)
          ·
            refine ⟨70342664464765311510312067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93790219286353748680416089 70342664464765311510312067)
            ·
              refine ⟨105513996697147967265468101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70342664464765311510312067 105513996697147967265468101)
              ·
                refine ⟨19783874380715243862275269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105513996697147967265468101 19783874380715243862275269)
                ·
                  refine ⟨3709476446384108224176613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19783874380715243862275269 3709476446384108224176613)
                  ·
                    refine ⟨695526833697020292033115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3709476446384108224176613 695526833697020292033115)
                    ·
                      rfl

theorem cell23_4063601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_4063601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063601 prefixEnd_4063601 := by exact prefixLift 4063601
  have htrace : WordTrace (prefixWord ++ tailWord_4063601) baseStart_4063601 baseEnd_4063601 := by
    simpa [prefixWord, tailWord_4063601, baseEnd_4063601] using wordTrace_append hprefix tailTrace_4063601
  have hstable : (prefixWord ++ tailWord_4063601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063601).length < 2 ^ (prefixWord ++ tailWord_4063601).sum := by decide
  have hdescent : baseEnd_4063601 < baseStart_4063601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063602 : List Nat := [3, 2, 1, 2, 1, 4, 2, 3, 1, 1, 3]
def baseStart_4063602 : Nat := 118140960795 + 4063602 * 2 ^ 59
def prefixEnd_4063602 : Nat := 4983230072969 + 3 ^ 40 * 4063602 * 2
def baseEnd_4063602 : Nat := 2086581014571715372186841

theorem tailTrace_4063602 : CollatzResearch.WordTrace tailWord_4063602 prefixEnd_4063602 2086581014571715372186841 := by
  unfold tailWord_4063602
  simp only [CollatzResearch.WordTrace]
  refine ⟨37052935256067859203478265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98807827349514291209275373 37052935256067859203478265)
  ·
    refine ⟨27789701442050894402608699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37052935256067859203478265 27789701442050894402608699)
    ·
      refine ⟨41684552163076341603913049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27789701442050894402608699 41684552163076341603913049)
      ·
        refine ⟨31263414122307256202934787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41684552163076341603913049 31263414122307256202934787)
        ·
          refine ⟨46895121183460884304402181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31263414122307256202934787 46895121183460884304402181)
          ·
            refine ⟨8792835221898915807075409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46895121183460884304402181 8792835221898915807075409)
            ·
              refine ⟨6594626416424186855306557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8792835221898915807075409 6594626416424186855306557)
              ·
                refine ⟨2472984906159070070739959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6594626416424186855306557 2472984906159070070739959)
                ·
                  refine ⟨3709477359238605106109939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472984906159070070739959 3709477359238605106109939)
                  ·
                    refine ⟨5564216038857907659164909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3709477359238605106109939 5564216038857907659164909)
                    ·
                      refine ⟨2086581014571715372186841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5564216038857907659164909 2086581014571715372186841)
                      ·
                        rfl

theorem cell23_4063602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_4063602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063602 prefixEnd_4063602 := by exact prefixLift 4063602
  have htrace : WordTrace (prefixWord ++ tailWord_4063602) baseStart_4063602 baseEnd_4063602 := by
    simpa [prefixWord, tailWord_4063602, baseEnd_4063602] using wordTrace_append hprefix tailTrace_4063602
  have hstable : (prefixWord ++ tailWord_4063602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063602).length < 2 ^ (prefixWord ++ tailWord_4063602).sum := by decide
  have hdescent : baseEnd_4063602 < baseStart_4063602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063605 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_4063605 : Nat := 118140960795 + 4063605 * 2 ^ 59
def prefixEnd_4063605 : Nat := 4983230072969 + 3 ^ 40 * 4063605 * 2
def baseEnd_4063605 : Nat := 695527518337892953483109

theorem tailTrace_4063605 : CollatzResearch.WordTrace tailWord_4063605 prefixEnd_4063605 695527518337892953483109 := by
  unfold tailWord_4063605
  simp only [CollatzResearch.WordTrace]
  refine ⟨148211850443260568326272269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98807900295507045550848179 148211850443260568326272269)
  ·
    refine ⟨55579443916222713122352101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148211850443260568326272269 55579443916222713122352101)
    ·
      refine ⟨10421145734291758710441019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55579443916222713122352101 10421145734291758710441019)
      ·
        refine ⟨15631718601437638065661529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10421145734291758710441019 15631718601437638065661529)
        ·
          refine ⟨11723788951078228549246147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15631718601437638065661529 11723788951078228549246147)
          ·
            refine ⟨17585683426617342823869221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11723788951078228549246147 17585683426617342823869221)
            ·
              refine ⟨3297315642490751779475479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17585683426617342823869221 3297315642490751779475479)
              ·
                refine ⟨4945973463736127669213219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297315642490751779475479 4945973463736127669213219)
                ·
                  refine ⟨7418960195604191503819829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4945973463736127669213219 7418960195604191503819829)
                  ·
                    refine ⟨695527518337892953483109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7418960195604191503819829 695527518337892953483109)
                    ·
                      rfl

theorem cell23_4063605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_4063605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063605 prefixEnd_4063605 := by exact prefixLift 4063605
  have htrace : WordTrace (prefixWord ++ tailWord_4063605) baseStart_4063605 baseEnd_4063605 := by
    simpa [prefixWord, tailWord_4063605, baseEnd_4063605] using wordTrace_append hprefix tailTrace_4063605
  have hstable : (prefixWord ++ tailWord_4063605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063605).length < 2 ^ (prefixWord ++ tailWord_4063605).sum := by decide
  have hdescent : baseEnd_4063605 < baseStart_4063605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063625 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 3, 2, 2]
def baseStart_4063625 : Nat := 118140960795 + 4063625 * 2 ^ 59
def prefixEnd_4063625 : Nat := 4983230072969 + 3 ^ 40 * 4063625 * 2
def baseEnd_4063625 : Nat := 2086592824626768782199235

theorem tailTrace_4063625 : CollatzResearch.WordTrace tailWord_4063625 prefixEnd_4063625 2086592824626768782199235 := by
  unfold tailWord_4063625
  simp only [CollatzResearch.WordTrace]
  refine ⟨148212579903188111742000329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98808386602125407828000219 148212579903188111742000329)
  ·
    refine ⟨111159434927391083806500247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148212579903188111742000329 111159434927391083806500247)
    ·
      refine ⟨166739152391086625709750371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111159434927391083806500247 166739152391086625709750371)
      ·
        refine ⟨250108728586629938564625557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166739152391086625709750371 250108728586629938564625557)
        ·
          refine ⟨11723846652498278370216823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 250108728586629938564625557 11723846652498278370216823)
          ·
            refine ⟨17585769978747417555325235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11723846652498278370216823 17585769978747417555325235)
            ·
              refine ⟨26378654968121126332987853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17585769978747417555325235 26378654968121126332987853)
              ·
                refine ⟨9891995613045422374870445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26378654968121126332987853 9891995613045422374870445)
                ·
                  refine ⟨3709498354892033390576417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9891995613045422374870445 3709498354892033390576417)
                  ·
                    refine ⟨2782123766169025042932313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3709498354892033390576417 2782123766169025042932313)
                    ·
                      refine ⟨2086592824626768782199235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782123766169025042932313 2086592824626768782199235)
                      ·
                        rfl

theorem cell23_4063625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 2, 2].length) (baseStart_4063625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063625 prefixEnd_4063625 := by exact prefixLift 4063625
  have htrace : WordTrace (prefixWord ++ tailWord_4063625) baseStart_4063625 baseEnd_4063625 := by
    simpa [prefixWord, tailWord_4063625, baseEnd_4063625] using wordTrace_append hprefix tailTrace_4063625
  have hstable : (prefixWord ++ tailWord_4063625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063625).length < 2 ^ (prefixWord ++ tailWord_4063625).sum := by decide
  have hdescent : baseEnd_4063625 < baseStart_4063625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063648 : List Nat := [2, 1, 1, 4, 1, 5, 2, 7]
def baseStart_4063648 : Nat := 118140960795 + 4063648 * 2 ^ 59
def prefixEnd_4063648 : Nat := 4983230072969 + 3 ^ 40 * 4063648 * 2
def baseEnd_4063648 : Nat := 77281653136363784896727

theorem tailTrace_4063648 : CollatzResearch.WordTrace tailWord_4063648 prefixEnd_4063648 77281653136363784896727 := by
  unfold tailWord_4063648
  simp only [CollatzResearch.WordTrace]
  refine ⟨74106709391052393335043799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98808945854736524446725065 74106709391052393335043799)
  ·
    refine ⟨111160064086578590002565699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74106709391052393335043799 111160064086578590002565699)
    ·
      refine ⟨166740096129867885003848549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111160064086578590002565699 166740096129867885003848549)
      ·
        refine ⟨31263768024350228438221603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166740096129867885003848549 31263768024350228438221603)
        ·
          refine ⟨46895652036525342657332405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31263768024350228438221603 46895652036525342657332405)
          ·
            refine ⟨4396467378424250874124913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46895652036525342657332405 4396467378424250874124913)
            ·
              refine ⟨3297350533818188155593685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4396467378424250874124913 3297350533818188155593685)
              ·
                refine ⟨77281653136363784896727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3297350533818188155593685 77281653136363784896727)
                ·
                  rfl

theorem cell23_4063648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 7].length) (baseStart_4063648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063648 prefixEnd_4063648 := by exact prefixLift 4063648
  have htrace : WordTrace (prefixWord ++ tailWord_4063648) baseStart_4063648 baseEnd_4063648 := by
    simpa [prefixWord, tailWord_4063648, baseEnd_4063648] using wordTrace_append hprefix tailTrace_4063648
  have hstable : (prefixWord ++ tailWord_4063648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063648).length < 2 ^ (prefixWord ++ tailWord_4063648).sum := by decide
  have hdescent : baseEnd_4063648 < baseStart_4063648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063676 : List Nat := [2, 2, 2, 4, 1, 2, 3, 2, 1, 2, 2]
def baseStart_4063676 : Nat := 118140960795 + 4063676 * 2 ^ 59
def prefixEnd_4063676 : Nat := 4983230072969 + 3 ^ 40 * 4063676 * 2
def baseEnd_4063676 : Nat := 2086619012140148082661501

theorem tailTrace_4063676 : CollatzResearch.WordTrace tailWord_4063676 prefixEnd_4063676 2086619012140148082661501 := by
  unfold tailWord_4063676
  simp only [CollatzResearch.WordTrace]
  refine ⟨74107220013001673726053441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98809626684002231634737921 74107220013001673726053441)
  ·
    refine ⟨55580415009751255294540081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74107220013001673726053441 55580415009751255294540081)
    ·
      refine ⟨41685311257313441470905061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55580415009751255294540081 41685311257313441470905061)
      ·
        refine ⟨7815995860746270275794699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41685311257313441470905061 7815995860746270275794699)
        ·
          refine ⟨11723993791119405413692049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815995860746270275794699 11723993791119405413692049)
          ·
            refine ⟨8792995343339554060269037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11723993791119405413692049 8792995343339554060269037)
            ·
              refine ⟨3297373253752332772600889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8792995343339554060269037 3297373253752332772600889)
              ·
                refine ⟨2473029940314249579450667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297373253752332772600889 2473029940314249579450667)
                ·
                  refine ⟨3709544910471374369176001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473029940314249579450667 3709544910471374369176001)
                  ·
                    refine ⟨2782158682853530776882001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3709544910471374369176001 2782158682853530776882001)
                    ·
                      refine ⟨2086619012140148082661501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782158682853530776882001 2086619012140148082661501)
                      ·
                        rfl

theorem cell23_4063676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_4063676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063676 prefixEnd_4063676 := by exact prefixLift 4063676
  have htrace : WordTrace (prefixWord ++ tailWord_4063676) baseStart_4063676 baseEnd_4063676 := by
    simpa [prefixWord, tailWord_4063676, baseEnd_4063676] using wordTrace_append hprefix tailTrace_4063676
  have hstable : (prefixWord ++ tailWord_4063676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063676).length < 2 ^ (prefixWord ++ tailWord_4063676).sum := by decide
  have hdescent : baseEnd_4063676 < baseStart_4063676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063692 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 2, 1, 3]
def baseStart_4063692 : Nat := 118140960795 + 4063692 * 2 ^ 59
def prefixEnd_4063692 : Nat := 4983230072969 + 3 ^ 40 * 4063692 * 2
def baseEnd_4063692 : Nat := 2086627227830620020061427

theorem tailTrace_4063692 : CollatzResearch.WordTrace tailWord_4063692 prefixEnd_4063692 2086627227830620020061427 := by
  unfold tailWord_4063692
  simp only [CollatzResearch.WordTrace]
  refine ⟨74107511796972691092344665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98810015729296921456459553 74107511796972691092344665)
  ·
    refine ⟨55580633847729518319258499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74107511796972691092344665 55580633847729518319258499)
    ·
      refine ⟨83370950771594277478887749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55580633847729518319258499 83370950771594277478887749)
      ·
        refine ⟨15632053269673927027291453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83370950771594277478887749 15632053269673927027291453)
        ·
          refine ⟨5862019976127722635234295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15632053269673927027291453 5862019976127722635234295)
          ·
            refine ⟨8793029964191583952851443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862019976127722635234295 8793029964191583952851443)
            ·
              refine ⟨13189544946287375929277165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793029964191583952851443 13189544946287375929277165)
              ·
                refine ⟨4946079354857765973478937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13189544946287375929277165 4946079354857765973478937)
                ·
                  refine ⟨3709559516143324480109203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4946079354857765973478937 3709559516143324480109203)
                  ·
                    refine ⟨5564339274214986720163805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3709559516143324480109203 5564339274214986720163805)
                    ·
                      refine ⟨2086627227830620020061427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5564339274214986720163805 2086627227830620020061427)
                      ·
                        rfl

theorem cell23_4063692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_4063692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063692 prefixEnd_4063692 := by exact prefixLift 4063692
  have htrace : WordTrace (prefixWord ++ tailWord_4063692) baseStart_4063692 baseEnd_4063692 := by
    simpa [prefixWord, tailWord_4063692, baseEnd_4063692] using wordTrace_append hprefix tailTrace_4063692
  have hstable : (prefixWord ++ tailWord_4063692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063692).length < 2 ^ (prefixWord ++ tailWord_4063692).sum := by decide
  have hdescent : baseEnd_4063692 < baseStart_4063692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063702 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_4063702 : Nat := 118140960795 + 4063702 * 2 ^ 59
def prefixEnd_4063702 : Nat := 4983230072969 + 3 ^ 40 * 4063702 * 2
def baseEnd_4063702 : Nat := 2086632362637164980936381

theorem tailTrace_4063702 : CollatzResearch.WordTrace tailWord_4063702 prefixEnd_4063702 2086632362637164980936381 := by
  unfold tailWord_4063702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9263461770244322118284585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98810258882606102595035573 9263461770244322118284585)
  ·
    refine ⟨6947596327683241588713439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9263461770244322118284585 6947596327683241588713439)
    ·
      refine ⟨10421394491524862383070159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6947596327683241588713439 10421394491524862383070159)
      ·
        refine ⟨15632091737287293574605239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10421394491524862383070159 15632091737287293574605239)
        ·
          refine ⟨23448137605930940361907859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15632091737287293574605239 23448137605930940361907859)
          ·
            refine ⟨35172206408896410542861789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23448137605930940361907859 35172206408896410542861789)
            ·
              refine ⟨13189577403336153953573171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35172206408896410542861789 13189577403336153953573171)
              ·
                refine ⟨19784366105004230930359757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13189577403336153953573171 19784366105004230930359757)
                ·
                  refine ⟨7419137289376586598884909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19784366105004230930359757 7419137289376586598884909)
                  ·
                    refine ⟨2782176483516219974581841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7419137289376586598884909 2782176483516219974581841)
                    ·
                      refine ⟨2086632362637164980936381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782176483516219974581841 2086632362637164980936381)
                      ·
                        rfl

theorem cell23_4063702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_4063702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063702 prefixEnd_4063702 := by exact prefixLift 4063702
  have htrace : WordTrace (prefixWord ++ tailWord_4063702) baseStart_4063702 baseEnd_4063702 := by
    simpa [prefixWord, tailWord_4063702, baseEnd_4063702] using wordTrace_append hprefix tailTrace_4063702
  have hstable : (prefixWord ++ tailWord_4063702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063702).length < 2 ^ (prefixWord ++ tailWord_4063702).sum := by decide
  have hdescent : baseEnd_4063702 < baseStart_4063702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063761 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_4063761 : Nat := 118140960795 + 4063761 * 2 ^ 59
def prefixEnd_4063761 : Nat := 4983230072969 + 3 ^ 40 * 4063761 * 2
def baseEnd_4063761 : Nat := 2086662657995780250098609

theorem tailTrace_4063761 : CollatzResearch.WordTrace tailWord_4063761 prefixEnd_4063761 2086662657995780250098609 := by
  unfold tailWord_4063761
  simp only [CollatzResearch.WordTrace]
  refine ⟨148217540230695406968951137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98811693487130271312634091 148217540230695406968951137)
  ·
    refine ⟨111163155173021555226713353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148217540230695406968951137 111163155173021555226713353)
    ·
      refine ⟨83372366379766166420035015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111163155173021555226713353 83372366379766166420035015)
      ·
        refine ⟨125058549569649249630052523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83372366379766166420035015 125058549569649249630052523)
        ·
          refine ⟨187587824354473874445078785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125058549569649249630052523 187587824354473874445078785)
          ·
            refine ⟨140690868265855405833809089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187587824354473874445078785 140690868265855405833809089)
            ·
              refine ⟨105518151199391554375356817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140690868265855405833809089 105518151199391554375356817)
              ·
                refine ⟨79138613399543665781517613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105518151199391554375356817 79138613399543665781517613)
                ·
                  refine ⟨29676980024828874668069105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79138613399543665781517613 29676980024828874668069105)
                  ·
                    refine ⟨22257735018621656001051829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29676980024828874668069105 22257735018621656001051829)
                    ·
                      refine ⟨2086662657995780250098609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22257735018621656001051829 2086662657995780250098609)
                      ·
                        rfl

theorem cell23_4063761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_4063761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063761 prefixEnd_4063761 := by exact prefixLift 4063761
  have htrace : WordTrace (prefixWord ++ tailWord_4063761) baseStart_4063761 baseEnd_4063761 := by
    simpa [prefixWord, tailWord_4063761, baseEnd_4063761] using wordTrace_append hprefix tailTrace_4063761
  have hstable : (prefixWord ++ tailWord_4063761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063761).length < 2 ^ (prefixWord ++ tailWord_4063761).sum := by decide
  have hdescent : baseEnd_4063761 < baseStart_4063761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063768 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 1, 7]
def baseStart_4063768 : Nat := 118140960795 + 4063768 * 2 ^ 59
def prefixEnd_4063768 : Nat := 4983230072969 + 3 ^ 40 * 4063768 * 2
def baseEnd_4063768 : Nat := 695555417453453907570359

theorem tailTrace_4063768 : CollatzResearch.WordTrace tailWord_4063768 prefixEnd_4063768 695555417453453907570359 := by
  unfold tailWord_4063768
  simp only [CollatzResearch.WordTrace]
  refine ⟨74108897770835023582227979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98811863694446698109637305 74108897770835023582227979)
  ·
    refine ⟨111163346656252535373341969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74108897770835023582227979 111163346656252535373341969)
    ·
      refine ⟨83372509992189401530006477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111163346656252535373341969 83372509992189401530006477)
      ·
        refine ⟨31264691247071025573752429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83372509992189401530006477 31264691247071025573752429)
        ·
          refine ⟨11724259217651634590157161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31264691247071025573752429 11724259217651634590157161)
          ·
            refine ⟨8793194413238725942617871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11724259217651634590157161 8793194413238725942617871)
            ·
              refine ⟨13189791619858088913926807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793194413238725942617871 13189791619858088913926807)
              ·
                refine ⟨19784687429787133370890211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13189791619858088913926807 19784687429787133370890211)
                ·
                  refine ⟨29677031144680700056335317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19784687429787133370890211 29677031144680700056335317)
                  ·
                    refine ⟨695555417453453907570359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29677031144680700056335317 695555417453453907570359)
                    ·
                      rfl

theorem cell23_4063768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_4063768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063768 prefixEnd_4063768 := by exact prefixLift 4063768
  have htrace : WordTrace (prefixWord ++ tailWord_4063768) baseStart_4063768 baseEnd_4063768 := by
    simpa [prefixWord, tailWord_4063768, baseEnd_4063768] using wordTrace_append hprefix tailTrace_4063768
  have hstable : (prefixWord ++ tailWord_4063768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063768).length < 2 ^ (prefixWord ++ tailWord_4063768).sum := by decide
  have hdescent : baseEnd_4063768 < baseStart_4063768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063783 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4063783 : Nat := 118140960795 + 4063783 * 2 ^ 59
def prefixEnd_4063783 : Nat := 4983230072969 + 3 ^ 40 * 4063783 * 2
def baseEnd_4063783 : Nat := 2086673954570179164023509

theorem tailTrace_4063783 : CollatzResearch.WordTrace tailWord_4063783 prefixEnd_4063783 2086673954570179164023509 := by
  unfold tailWord_4063783
  simp only [CollatzResearch.WordTrace]
  refine ⟨148218342636615704726252003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98812228424410469817501335 148218342636615704726252003)
  ·
    refine ⟨222327513954923557089378005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148218342636615704726252003 222327513954923557089378005)
    ·
      refine ⟨5210801108318520869282297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 222327513954923557089378005 5210801108318520869282297)
      ·
        refine ⟨3908100831238890651961723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5210801108318520869282297 3908100831238890651961723)
        ·
          refine ⟨5862151246858335977942585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908100831238890651961723 5862151246858335977942585)
          ·
            refine ⟨4396613435143751983456939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5862151246858335977942585 4396613435143751983456939)
            ·
              refine ⟨6594920152715627975185409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396613435143751983456939 6594920152715627975185409)
              ·
                refine ⟨4946190114536720981389057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6594920152715627975185409 4946190114536720981389057)
                ·
                  refine ⟨3709642585902540736041793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4946190114536720981389057 3709642585902540736041793)
                  ·
                    refine ⟨2782231939426905552031345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3709642585902540736041793 2782231939426905552031345)
                    ·
                      refine ⟨2086673954570179164023509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782231939426905552031345 2086673954570179164023509)
                      ·
                        rfl

theorem cell23_4063783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4063783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063783 prefixEnd_4063783 := by exact prefixLift 4063783
  have htrace : WordTrace (prefixWord ++ tailWord_4063783) baseStart_4063783 baseEnd_4063783 := by
    simpa [prefixWord, tailWord_4063783, baseEnd_4063783] using wordTrace_append hprefix tailTrace_4063783
  have hstable : (prefixWord ++ tailWord_4063783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063783).length < 2 ^ (prefixWord ++ tailWord_4063783).sum := by decide
  have hdescent : baseEnd_4063783 < baseStart_4063783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063788 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_4063788 : Nat := 118140960795 + 4063788 * 2 ^ 59
def prefixEnd_4063788 : Nat := 4983230072969 + 3 ^ 40 * 4063788 * 2
def baseEnd_4063788 : Nat := 2086676521973451644460985

theorem tailTrace_4063788 : CollatzResearch.WordTrace tailWord_4063788 prefixEnd_4063788 2086676521973451644460985 := by
  unfold tailWord_4063788
  simp only [CollatzResearch.WordTrace]
  refine ⟨74109262500798795290092009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98812350001065060386789345 74109262500798795290092009)
  ·
    refine ⟨55581946875599096467569007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74109262500798795290092009 55581946875599096467569007)
    ·
      refine ⟨83372920313398644701353511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55581946875599096467569007 83372920313398644701353511)
      ·
        refine ⟨125059380470097967052030267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83372920313398644701353511 125059380470097967052030267)
        ·
          refine ⟨187589070705146950578045401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125059380470097967052030267 187589070705146950578045401)
          ·
            refine ⟨140691803028860212933534051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187589070705146950578045401 140691803028860212933534051)
            ·
              refine ⟨211037704543290319400301077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140691803028860212933534051 211037704543290319400301077)
              ·
                refine ⟨9892392400466733721889113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211037704543290319400301077 9892392400466733721889113)
                ·
                  refine ⟨7419294300350050291416835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9892392400466733721889113 7419294300350050291416835)
                  ·
                    refine ⟨11128941450525075437125253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7419294300350050291416835 11128941450525075437125253)
                    ·
                      refine ⟨2086676521973451644460985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11128941450525075437125253 2086676521973451644460985)
                      ·
                        rfl

theorem cell23_4063788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_4063788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063788 prefixEnd_4063788 := by exact prefixLift 4063788
  have htrace : WordTrace (prefixWord ++ tailWord_4063788) baseStart_4063788 baseEnd_4063788 := by
    simpa [prefixWord, tailWord_4063788, baseEnd_4063788] using wordTrace_append hprefix tailTrace_4063788
  have hstable : (prefixWord ++ tailWord_4063788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063788).length < 2 ^ (prefixWord ++ tailWord_4063788).sum := by decide
  have hdescent : baseEnd_4063788 < baseStart_4063788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063789 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 7]
def baseStart_4063789 : Nat := 118140960795 + 4063789 * 2 ^ 59
def prefixEnd_4063789 : Nat := 4983230072969 + 3 ^ 40 * 4063789 * 2
def baseEnd_4063789 : Nat := 231853003939345126727609

theorem tailTrace_4063789 : CollatzResearch.WordTrace tailWord_4063789 prefixEnd_4063789 231853003939345126727609 := by
  unfold tailWord_4063789
  simp only [CollatzResearch.WordTrace]
  refine ⟨148218561474593967750970421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98812374316395978500646947 148218561474593967750970421)
  ·
    refine ⟨13895490138243184476653477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148218561474593967750970421 13895490138243184476653477)
    ·
      refine ⟨2605404400920597089372527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13895490138243184476653477 2605404400920597089372527)
      ·
        refine ⟨3908106601380895634058791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2605404400920597089372527 3908106601380895634058791)
        ·
          refine ⟨5862159902071343451088187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908106601380895634058791 5862159902071343451088187)
          ·
            refine ⟨8793239853107015176632281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862159902071343451088187 8793239853107015176632281)
            ·
              refine ⟨6594929889830261382474211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8793239853107015176632281 6594929889830261382474211)
              ·
                refine ⟨9892394834745392073711317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594929889830261382474211 9892394834745392073711317)
                ·
                  refine ⟨231853003939345126727609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9892394834745392073711317 231853003939345126727609)
                  ·
                    rfl

theorem cell23_4063789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_4063789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063789 prefixEnd_4063789 := by exact prefixLift 4063789
  have htrace : WordTrace (prefixWord ++ tailWord_4063789) baseStart_4063789 baseEnd_4063789 := by
    simpa [prefixWord, tailWord_4063789, baseEnd_4063789] using wordTrace_append hprefix tailTrace_4063789
  have hstable : (prefixWord ++ tailWord_4063789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063789).length < 2 ^ (prefixWord ++ tailWord_4063789).sum := by decide
  have hdescent : baseEnd_4063789 < baseStart_4063789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063808 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 3]
def baseStart_4063808 : Nat := 118140960795 + 4063808 * 2 ^ 59
def prefixEnd_4063808 : Nat := 4983230072969 + 3 ^ 40 * 4063808 * 2
def baseEnd_4063808 : Nat := 2086686791586541566210893

theorem tailTrace_4063808 : CollatzResearch.WordTrace tailWord_4063808 prefixEnd_4063808 2086686791586541566210893 := by
  unfold tailWord_4063808
  simp only [CollatzResearch.WordTrace]
  refine ⟨74109627230762566997956039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98812836307683422663941385 74109627230762566997956039)
  ·
    refine ⟨111164440846143850496934059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74109627230762566997956039 111164440846143850496934059)
    ·
      refine ⟨166746661269215775745401089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111164440846143850496934059 166746661269215775745401089)
      ·
        refine ⟨125059995951911831809050817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166746661269215775745401089 125059995951911831809050817)
        ·
          refine ⟨93794996963933873856788113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125059995951911831809050817 93794996963933873856788113)
          ·
            refine ⟨70346247722950405392591085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93794996963933873856788113 70346247722950405392591085)
            ·
              refine ⟨26379842896106402022221657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70346247722950405392591085 26379842896106402022221657)
              ·
                refine ⟨19784882172079801516666243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26379842896106402022221657 19784882172079801516666243)
                ·
                  refine ⟨29677323258119702274999365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19784882172079801516666243 29677323258119702274999365)
                  ·
                    refine ⟨5564498110897444176562381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29677323258119702274999365 5564498110897444176562381)
                    ·
                      refine ⟨2086686791586541566210893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5564498110897444176562381 2086686791586541566210893)
                      ·
                        rfl

theorem cell23_4063808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_4063808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063808 prefixEnd_4063808 := by exact prefixLift 4063808
  have htrace : WordTrace (prefixWord ++ tailWord_4063808) baseStart_4063808 baseEnd_4063808 := by
    simpa [prefixWord, tailWord_4063808, baseEnd_4063808] using wordTrace_append hprefix tailTrace_4063808
  have hstable : (prefixWord ++ tailWord_4063808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063808).length < 2 ^ (prefixWord ++ tailWord_4063808).sum := by decide
  have hdescent : baseEnd_4063808 < baseStart_4063808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063815 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 3, 4]
def baseStart_4063815 : Nat := 118140960795 + 4063815 * 2 ^ 59
def prefixEnd_4063815 : Nat := 4983230072969 + 3 ^ 40 * 4063815 * 2
def baseEnd_4063815 : Nat := 695563461983707679607787

theorem tailTrace_4063815 : CollatzResearch.WordTrace tailWord_4063815 prefixEnd_4063815 695563461983707679607787 := by
  unfold tailWord_4063815
  simp only [CollatzResearch.WordTrace]
  refine ⟨148219509772499774191416899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98813006514999849460944599 148219509772499774191416899)
  ·
    refine ⟨222329264658749661287125349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148219509772499774191416899 222329264658749661287125349)
    ·
      refine ⟨41686737123515561491336003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222329264658749661287125349 41686737123515561491336003)
      ·
        refine ⟨62530105685273342237004005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41686737123515561491336003 62530105685273342237004005)
        ·
          refine ⟨11724394815988751669438251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62530105685273342237004005 11724394815988751669438251)
          ·
            refine ⟨17586592223983127504157377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11724394815988751669438251 17586592223983127504157377)
            ·
              refine ⟨13189944167987345628118033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17586592223983127504157377 13189944167987345628118033)
              ·
                refine ⟨9892458125990509221088525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13189944167987345628118033 9892458125990509221088525)
                ·
                  refine ⟨3709671797246440957908197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9892458125990509221088525 3709671797246440957908197)
                  ·
                    refine ⟨695563461983707679607787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3709671797246440957908197 695563461983707679607787)
                    ·
                      rfl

theorem cell23_4063815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_4063815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063815 prefixEnd_4063815 := by exact prefixLift 4063815
  have htrace : WordTrace (prefixWord ++ tailWord_4063815) baseStart_4063815 baseEnd_4063815 := by
    simpa [prefixWord, tailWord_4063815, baseEnd_4063815] using wordTrace_append hprefix tailTrace_4063815
  have hstable : (prefixWord ++ tailWord_4063815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063815).length < 2 ^ (prefixWord ++ tailWord_4063815).sum := by decide
  have hdescent : baseEnd_4063815 < baseStart_4063815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063828 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 8]
def baseStart_4063828 : Nat := 118140960795 + 4063828 * 2 ^ 59
def prefixEnd_4063828 : Nat := 4983230072969 + 3 ^ 40 * 4063828 * 2
def baseEnd_4063828 : Nat := 231855229022181276440089

theorem tailTrace_4063828 : CollatzResearch.WordTrace tailWord_4063828 prefixEnd_4063828 231855229022181276440089 := by
  unfold tailWord_4063828
  simp only [CollatzResearch.WordTrace]
  refine ⟨74109991960726338705820069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98813322614301784941093425 74109991960726338705820069)
  ·
    refine ⟨13895623492636188507341263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74109991960726338705820069 13895623492636188507341263)
    ·
      refine ⟨20843435238954282761011895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13895623492636188507341263 20843435238954282761011895)
      ·
        refine ⟨31265152858431424141517843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20843435238954282761011895 31265152858431424141517843)
        ·
          refine ⟨46897729287647136212276765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31265152858431424141517843 46897729287647136212276765)
          ·
            refine ⟨17586648482867676079603787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46897729287647136212276765 17586648482867676079603787)
            ·
              refine ⟨26379972724301514119405681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17586648482867676079603787 26379972724301514119405681)
              ·
                refine ⟨19784979543226135589554261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26379972724301514119405681 19784979543226135589554261)
                ·
                  refine ⟨231855229022181276440089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19784979543226135589554261 231855229022181276440089)
                  ·
                    rfl

theorem cell23_4063828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_4063828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063828 prefixEnd_4063828 := by exact prefixLift 4063828
  have htrace : WordTrace (prefixWord ++ tailWord_4063828) baseStart_4063828 baseEnd_4063828 := by
    simpa [prefixWord, tailWord_4063828, baseEnd_4063828] using wordTrace_append hprefix tailTrace_4063828
  have hstable : (prefixWord ++ tailWord_4063828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063828).length < 2 ^ (prefixWord ++ tailWord_4063828).sum := by decide
  have hdescent : baseEnd_4063828 < baseStart_4063828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063832 : List Nat := [2, 1, 2, 2, 1, 2, 5, 3, 1, 4]
def baseStart_4063832 : Nat := 118140960795 + 4063832 * 2 ^ 59
def prefixEnd_4063832 : Nat := 4983230072969 + 3 ^ 40 * 4063832 * 2
def baseEnd_4063832 : Nat := 695566371707416490770261

theorem tailTrace_4063832 : CollatzResearch.WordTrace tailWord_4063832 prefixEnd_4063832 695566371707416490770261 := by
  unfold tailWord_4063832
  simp only [CollatzResearch.WordTrace]
  refine ⟨74110064906719093047392875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98813419875625457396523833 74110064906719093047392875)
  ·
    refine ⟨111165097360078639571089313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74110064906719093047392875 111165097360078639571089313)
    ·
      refine ⟨83373823020058979678316985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111165097360078639571089313 83373823020058979678316985)
      ·
        refine ⟨62530367265044234758737739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83373823020058979678316985 62530367265044234758737739)
        ·
          refine ⟨93795550897566352138106609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62530367265044234758737739 93795550897566352138106609)
          ·
            refine ⟨70346663173174764103579957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93795550897566352138106609 70346663173174764103579957)
            ·
              refine ⟨6594999672485134134710621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70346663173174764103579957 6594999672485134134710621)
              ·
                refine ⟨2473124877181925300516483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6594999672485134134710621 2473124877181925300516483)
                ·
                  refine ⟨3709687315772887950774725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473124877181925300516483 3709687315772887950774725)
                  ·
                    refine ⟨695566371707416490770261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3709687315772887950774725 695566371707416490770261)
                    ·
                      rfl

theorem cell23_4063832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_4063832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063832 prefixEnd_4063832 := by exact prefixLift 4063832
  have htrace : WordTrace (prefixWord ++ tailWord_4063832) baseStart_4063832 baseEnd_4063832 := by
    simpa [prefixWord, tailWord_4063832, baseEnd_4063832] using wordTrace_append hprefix tailTrace_4063832
  have hstable : (prefixWord ++ tailWord_4063832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063832).length < 2 ^ (prefixWord ++ tailWord_4063832).sum := by decide
  have hdescent : baseEnd_4063832 < baseStart_4063832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063862 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_4063862 : Nat := 118140960795 + 4063862 * 2 ^ 59
def prefixEnd_4063862 : Nat := 4983230072969 + 3 ^ 40 * 4063862 * 2
def baseEnd_4063862 : Nat := 231857168837987150548405

theorem tailTrace_4063862 : CollatzResearch.WordTrace tailWord_4063862 prefixEnd_4063862 231857168837987150548405 := by
  unfold tailWord_4063862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9263826500208093826148615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98814149335553000812251893 9263826500208093826148615)
  ·
    refine ⟨13895739750312140739222923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9263826500208093826148615 13895739750312140739222923)
    ·
      refine ⟨20843609625468211108834385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13895739750312140739222923 20843609625468211108834385)
      ·
        refine ⟨15632707219101158331625789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20843609625468211108834385 15632707219101158331625789)
        ·
          refine ⟨5862265207162934374359671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15632707219101158331625789 5862265207162934374359671)
          ·
            refine ⟨8793397810744401561539507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862265207162934374359671 8793397810744401561539507)
            ·
              refine ⟨13190096716116602342309261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793397810744401561539507 13190096716116602342309261)
              ·
                refine ⟨4946286268543725878365973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13190096716116602342309261 4946286268543725878365973)
                ·
                  refine ⟨231857168837987150548405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4946286268543725878365973 231857168837987150548405)
                  ·
                    rfl

theorem cell23_4063862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_4063862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063862 prefixEnd_4063862 := by exact prefixLift 4063862
  have htrace : WordTrace (prefixWord ++ tailWord_4063862) baseStart_4063862 baseEnd_4063862 := by
    simpa [prefixWord, tailWord_4063862, baseEnd_4063862] using wordTrace_append hprefix tailTrace_4063862
  have hstable : (prefixWord ++ tailWord_4063862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063862).length < 2 ^ (prefixWord ++ tailWord_4063862).sum := by decide
  have hdescent : baseEnd_4063862 < baseStart_4063862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063875 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 1, 5]
def baseStart_4063875 : Nat := 118140960795 + 4063875 * 2 ^ 59
def prefixEnd_4063875 : Nat := 4983230072969 + 3 ^ 40 * 4063875 * 2
def baseEnd_4063875 : Nat := 695573731596797601357695

theorem tailTrace_4063875 : CollatzResearch.WordTrace tailWord_4063875 prefixEnd_4063875 695573731596797601357695 := by
  unfold tailWord_4063875
  simp only [CollatzResearch.WordTrace]
  refine ⟨148221698152282404438601079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98814465434854936292400719 148221698152282404438601079)
  ·
    refine ⟨222332547228423606657901619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148221698152282404438601079 222332547228423606657901619)
    ·
      refine ⟨333498820842635409986852429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222332547228423606657901619 333498820842635409986852429)
      ·
        refine ⟨125062057815988278745069661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333498820842635409986852429 125062057815988278745069661)
        ·
          refine ⟨46898271680995604529401123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125062057815988278745069661 46898271680995604529401123)
          ·
            refine ⟨70347407521493406794101685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46898271680995604529401123 70347407521493406794101685)
            ·
              refine ⟨6595069455140006886947033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70347407521493406794101685 6595069455140006886947033)
              ·
                refine ⟨4946302091355005165210275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6595069455140006886947033 4946302091355005165210275)
                ·
                  refine ⟨7419453137032507747815413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946302091355005165210275 7419453137032507747815413)
                  ·
                    refine ⟨695573731596797601357695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7419453137032507747815413 695573731596797601357695)
                    ·
                      rfl

theorem cell23_4063875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 5].length) (baseStart_4063875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063875 prefixEnd_4063875 := by exact prefixLift 4063875
  have htrace : WordTrace (prefixWord ++ tailWord_4063875) baseStart_4063875 baseEnd_4063875 := by
    simpa [prefixWord, tailWord_4063875, baseEnd_4063875] using wordTrace_append hprefix tailTrace_4063875
  have hstable : (prefixWord ++ tailWord_4063875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063875).length < 2 ^ (prefixWord ++ tailWord_4063875).sum := by decide
  have hdescent : baseEnd_4063875 < baseStart_4063875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063932 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_4063932 : Nat := 118140960795 + 4063932 * 2 ^ 59
def prefixEnd_4063932 : Nat := 4983230072969 + 3 ^ 40 * 4063932 * 2
def baseEnd_4063932 : Nat := 2086750463187699081060323

theorem tailTrace_4063932 : CollatzResearch.WordTrace tailWord_4063932 prefixEnd_4063932 2086750463187699081060323 := by
  unfold tailWord_4063932
  simp only [CollatzResearch.WordTrace]
  refine ⟨74111888556537951586713025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98815851408717268782284033 74111888556537951586713025)
  ·
    refine ⟨55583916417403463690034769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74111888556537951586713025 55583916417403463690034769)
    ·
      refine ⟨41687937313052597767526077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55583916417403463690034769 41687937313052597767526077)
      ·
        refine ⟨15632976492394724162822279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41687937313052597767526077 15632976492394724162822279)
        ·
          refine ⟨23449464738592086244233419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15632976492394724162822279 23449464738592086244233419)
          ·
            refine ⟨35174197107888129366350129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23449464738592086244233419 35174197107888129366350129)
            ·
              refine ⟨26380647830916097024762597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35174197107888129366350129 26380647830916097024762597)
              ·
                refine ⟨4946371468296768192142987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26380647830916097024762597 4946371468296768192142987)
                ·
                  refine ⟨7419557202445152288214481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946371468296768192142987 7419557202445152288214481)
                  ·
                    refine ⟨5564667901833864216160861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7419557202445152288214481 5564667901833864216160861)
                    ·
                      refine ⟨2086750463187699081060323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5564667901833864216160861 2086750463187699081060323)
                      ·
                        rfl

theorem cell23_4063932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_4063932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063932 prefixEnd_4063932 := by exact prefixLift 4063932
  have htrace : WordTrace (prefixWord ++ tailWord_4063932) baseStart_4063932 baseEnd_4063932 := by
    simpa [prefixWord, tailWord_4063932, baseEnd_4063932] using wordTrace_append hprefix tailTrace_4063932
  have hstable : (prefixWord ++ tailWord_4063932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063932).length < 2 ^ (prefixWord ++ tailWord_4063932).sum := by decide
  have hdescent : baseEnd_4063932 < baseStart_4063932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063935 : List Nat := [1, 1, 2, 2, 2, 5, 3, 7]
def baseStart_4063935 : Nat := 118140960795 + 4063935 * 2 ^ 59
def prefixEnd_4063935 : Nat := 4983230072969 + 3 ^ 40 * 4063935 * 2
def baseEnd_4063935 : Nat := 77287111245543058123067

theorem tailTrace_4063935 : CollatzResearch.WordTrace tailWord_4063935 prefixEnd_4063935 77287111245543058123067 := by
  unfold tailWord_4063935
  simp only [CollatzResearch.WordTrace]
  refine ⟨148223886532065034685785259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98815924354710023123856839 148223886532065034685785259)
  ·
    refine ⟨222335829798097552028677889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148223886532065034685785259 222335829798097552028677889)
    ·
      refine ⟨166751872348573164021508417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222335829798097552028677889 166751872348573164021508417)
      ·
        refine ⟨125063904261429873016131313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166751872348573164021508417 125063904261429873016131313)
        ·
          refine ⟨93797928196072404762098485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125063904261429873016131313 93797928196072404762098485)
          ·
            refine ⟨8793555768381787946446733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93797928196072404762098485 8793555768381787946446733)
            ·
              refine ⟨3297583413143170479917525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8793555768381787946446733 3297583413143170479917525)
              ·
                refine ⟨77287111245543058123067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3297583413143170479917525 77287111245543058123067)
                ·
                  rfl

theorem cell23_4063935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 7].length) (baseStart_4063935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063935 prefixEnd_4063935 := by exact prefixLift 4063935
  have htrace : WordTrace (prefixWord ++ tailWord_4063935) baseStart_4063935 baseEnd_4063935 := by
    simpa [prefixWord, tailWord_4063935, baseEnd_4063935] using wordTrace_append hprefix tailTrace_4063935
  have hstable : (prefixWord ++ tailWord_4063935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063935).length < 2 ^ (prefixWord ++ tailWord_4063935).sum := by decide
  have hdescent : baseEnd_4063935 < baseStart_4063935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063946 : List Nat := [3, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2]
def baseStart_4063946 : Nat := 118140960795 + 4063946 * 2 ^ 59
def prefixEnd_4063946 : Nat := 4983230072969 + 3 ^ 40 * 4063946 * 2
def baseEnd_4063946 : Nat := 2086757651916862026285259

theorem tailTrace_4063946 : CollatzResearch.WordTrace tailWord_4063946 prefixEnd_4063946 2086757651916862026285259 := by
  unfold tailWord_4063946
  simp only [CollatzResearch.WordTrace]
  refine ⟨37056071933756295891108923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98816191823350122376290461 37056071933756295891108923)
  ·
    refine ⟨55584107900634443836663385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37056071933756295891108923 55584107900634443836663385)
    ·
      refine ⟨41688080925475832877497539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55584107900634443836663385 41688080925475832877497539)
      ·
        refine ⟨62532121388213749316246309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41688080925475832877497539 62532121388213749316246309)
        ·
          refine ⟨11724772760290077996796183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62532121388213749316246309 11724772760290077996796183)
          ·
            refine ⟨17587159140435116995194275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11724772760290077996796183 17587159140435116995194275)
            ·
              refine ⟨26380738710652675492791413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17587159140435116995194275 26380738710652675492791413)
              ·
                refine ⟨2473194254123688327449195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26380738710652675492791413 2473194254123688327449195)
                ·
                  refine ⟨3709791381185532491173793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473194254123688327449195 3709791381185532491173793)
                  ·
                    refine ⟨2782343535889149368380345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3709791381185532491173793 2782343535889149368380345)
                    ·
                      refine ⟨2086757651916862026285259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782343535889149368380345 2086757651916862026285259)
                      ·
                        rfl

theorem cell23_4063946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_4063946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063946 prefixEnd_4063946 := by exact prefixLift 4063946
  have htrace : WordTrace (prefixWord ++ tailWord_4063946) baseStart_4063946 baseEnd_4063946 := by
    simpa [prefixWord, tailWord_4063946, baseEnd_4063946] using wordTrace_append hprefix tailTrace_4063946
  have hstable : (prefixWord ++ tailWord_4063946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063946).length < 2 ^ (prefixWord ++ tailWord_4063946).sum := by decide
  have hdescent : baseEnd_4063946 < baseStart_4063946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063956 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_4063956 : Nat := 118140960795 + 4063956 * 2 ^ 59
def prefixEnd_4063956 : Nat := 4983230072969 + 3 ^ 40 * 4063956 * 2
def baseEnd_4063956 : Nat := 695587595574468995720071

theorem tailTrace_4063956 : CollatzResearch.WordTrace tailWord_4063956 prefixEnd_4063956 695587595574468995720071 := by
  unfold tailWord_4063956
  simp only [CollatzResearch.WordTrace]
  refine ⟨74112326232494477636149861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98816434976659303514866481 74112326232494477636149861)
  ·
    refine ⟨13896061168592714556778099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74112326232494477636149861 13896061168592714556778099)
    ·
      refine ⟨20844091752889071835167149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13896061168592714556778099 20844091752889071835167149)
      ·
        refine ⟨7816534407333401938187681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20844091752889071835167149 7816534407333401938187681)
        ·
          refine ⟨5862400805500051453640761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7816534407333401938187681 5862400805500051453640761)
          ·
            refine ⟨4396800604125038590230571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5862400805500051453640761 4396800604125038590230571)
            ·
              refine ⟨6595200906187557885345857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396800604125038590230571 6595200906187557885345857)
              ·
                refine ⟨4946400679640668414009393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6595200906187557885345857 4946400679640668414009393)
                ·
                  refine ⟨3709800509730501310507045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4946400679640668414009393 3709800509730501310507045)
                  ·
                    refine ⟨695587595574468995720071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3709800509730501310507045 695587595574468995720071)
                    ·
                      rfl

theorem cell23_4063956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_4063956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063956 prefixEnd_4063956 := by exact prefixLift 4063956
  have htrace : WordTrace (prefixWord ++ tailWord_4063956) baseStart_4063956 baseEnd_4063956 := by
    simpa [prefixWord, tailWord_4063956, baseEnd_4063956] using wordTrace_append hprefix tailTrace_4063956
  have hstable : (prefixWord ++ tailWord_4063956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063956).length < 2 ^ (prefixWord ++ tailWord_4063956).sum := by decide
  have hdescent : baseEnd_4063956 < baseStart_4063956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063962 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3]
def baseStart_4063962 : Nat := 118140960795 + 4063962 * 2 ^ 59
def prefixEnd_4063962 : Nat := 4983230072969 + 3 ^ 40 * 4063962 * 2
def baseEnd_4063962 : Nat := 2086765867607333963685185

theorem tailTrace_4063962 : CollatzResearch.WordTrace tailWord_4063962 prefixEnd_4063962 2086765867607333963685185 := by
  unfold tailWord_4063962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37056217825741804574254535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98816580868644812198012093 37056217825741804574254535)
  ·
    refine ⟨55584326738612706861381803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37056217825741804574254535 55584326738612706861381803)
    ·
      refine ⟨83376490107919060292072705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55584326738612706861381803 83376490107919060292072705)
      ·
        refine ⟨62532367580939295219054529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83376490107919060292072705 62532367580939295219054529)
        ·
          refine ⟨46899275685704471414290897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62532367580939295219054529 46899275685704471414290897)
          ·
            refine ⟨35174456764278353560718173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46899275685704471414290897 35174456764278353560718173)
            ·
              refine ⟨13190421286604382585269315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35174456764278353560718173 13190421286604382585269315)
              ·
                refine ⟨19785631929906573877903973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13190421286604382585269315 19785631929906573877903973)
                ·
                  refine ⟨3709805986857482602106995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19785631929906573877903973 3709805986857482602106995)
                  ·
                    refine ⟨5564708980286223903160493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3709805986857482602106995 5564708980286223903160493)
                    ·
                      refine ⟨2086765867607333963685185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5564708980286223903160493 2086765867607333963685185)
                      ·
                        rfl

theorem cell23_4063962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_4063962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4063962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4063962 prefixEnd_4063962 := by exact prefixLift 4063962
  have htrace : WordTrace (prefixWord ++ tailWord_4063962) baseStart_4063962 baseEnd_4063962 := by
    simpa [prefixWord, tailWord_4063962, baseEnd_4063962] using wordTrace_append hprefix tailTrace_4063962
  have hstable : (prefixWord ++ tailWord_4063962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063962).length < 2 ^ (prefixWord ++ tailWord_4063962).sum := by decide
  have hdescent : baseEnd_4063962 < baseStart_4063962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064019 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 2, 2, 2]
def baseStart_4064019 : Nat := 118140960795 + 4064019 * 2 ^ 59
def prefixEnd_4064019 : Nat := 4983230072969 + 3 ^ 40 * 4064019 * 2
def baseEnd_4064019 : Nat := 2086795136004640240672423

theorem tailTrace_4064019 : CollatzResearch.WordTrace tailWord_4064019 prefixEnd_4064019 2086795136004640240672423 := by
  unfold tailWord_4064019
  simp only [CollatzResearch.WordTrace]
  refine ⟨148226950263760717031843111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98817966842507144687895407 148226950263760717031843111)
  ·
    refine ⟨222340425395641075547764667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148226950263760717031843111 222340425395641075547764667)
    ·
      refine ⟨333510638093461613321647001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222340425395641075547764667 333510638093461613321647001)
      ·
        refine ⟨250132978570096209991235251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333510638093461613321647001 250132978570096209991235251)
        ·
          refine ⟨375199467855144314986852877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250132978570096209991235251 375199467855144314986852877)
          ·
            refine ⟨140699800445679118120069829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375199467855144314986852877 140699800445679118120069829)
            ·
              refine ⟨26381212583564834647513093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140699800445679118120069829 26381212583564834647513093)
              ·
                refine ⟨4946477359418406496408705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26381212583564834647513093 4946477359418406496408705)
                ·
                  refine ⟨3709858019563804872306529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4946477359418406496408705 3709858019563804872306529)
                  ·
                    refine ⟨2782393514672853654229897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3709858019563804872306529 2782393514672853654229897)
                    ·
                      refine ⟨2086795136004640240672423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782393514672853654229897 2086795136004640240672423)
                      ·
                        rfl

theorem cell23_4064019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 2, 2].length) (baseStart_4064019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064019 prefixEnd_4064019 := by exact prefixLift 4064019
  have htrace : WordTrace (prefixWord ++ tailWord_4064019) baseStart_4064019 baseEnd_4064019 := by
    simpa [prefixWord, tailWord_4064019, baseEnd_4064019] using wordTrace_append hprefix tailTrace_4064019
  have hstable : (prefixWord ++ tailWord_4064019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064019).length < 2 ^ (prefixWord ++ tailWord_4064019).sum := by decide
  have hdescent : baseEnd_4064019 < baseStart_4064019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064035 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 3]
def baseStart_4064035 : Nat := 118140960795 + 4064035 * 2 ^ 59
def prefixEnd_4064035 : Nat := 4983230072969 + 3 ^ 40 * 4064035 * 2
def baseEnd_4064035 : Nat := 2086803351695112178072349

theorem tailTrace_4064035 : CollatzResearch.WordTrace tailWord_4064035 prefixEnd_4064035 2086803351695112178072349 := by
  unfold tailWord_4064035
  simp only [CollatzResearch.WordTrace]
  refine ⟨148227533831702751764425559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98818355887801834509617039 148227533831702751764425559)
  ·
    refine ⟨222341300747554127646638339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148227533831702751764425559 222341300747554127646638339)
    ·
      refine ⟨333511951121331191469957509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222341300747554127646638339 333511951121331191469957509)
      ·
        refine ⟨62533490835249598400617033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333511951121331191469957509 62533490835249598400617033)
        ·
          refine ⟨46900118126437198800462775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62533490835249598400617033 46900118126437198800462775)
          ·
            refine ⟨70350177189655798200694163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46900118126437198800462775 70350177189655798200694163)
            ·
              refine ⟨105525265784483697301041245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70350177189655798200694163 105525265784483697301041245)
              ·
                refine ⟨39571974669181386487890467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105525265784483697301041245 39571974669181386487890467)
                ·
                  refine ⟨59357962003772079731835701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39571974669181386487890467 59357962003772079731835701)
                  ·
                    refine ⟨5564808937853632474859597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59357962003772079731835701 5564808937853632474859597)
                    ·
                      refine ⟨2086803351695112178072349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5564808937853632474859597 2086803351695112178072349)
                      ·
                        rfl

theorem cell23_4064035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_4064035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064035 prefixEnd_4064035 := by exact prefixLift 4064035
  have htrace : WordTrace (prefixWord ++ tailWord_4064035) baseStart_4064035 baseEnd_4064035 := by
    simpa [prefixWord, tailWord_4064035, baseEnd_4064035] using wordTrace_append hprefix tailTrace_4064035
  have hstable : (prefixWord ++ tailWord_4064035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064035).length < 2 ^ (prefixWord ++ tailWord_4064035).sum := by decide
  have hdescent : baseEnd_4064035 < baseStart_4064035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064076 : List Nat := [2, 2, 1, 3, 3, 3, 2, 2, 5]
def baseStart_4064076 : Nat := 118140960795 + 4064076 * 2 ^ 59
def prefixEnd_4064076 : Nat := 4983230072969 + 3 ^ 40 * 4064076 * 2
def baseEnd_4064076 : Nat := 231869378266882946406629

theorem tailTrace_4064076 : CollatzResearch.WordTrace tailWord_4064076 prefixEnd_4064076 231869378266882946406629 := by
  unfold tailWord_4064076
  simp only [CollatzResearch.WordTrace]
  refine ⟨74114514612277107883334041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98819352816369477177778721 74114514612277107883334041)
  ·
    refine ⟨55585885959207830912500531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74114514612277107883334041 55585885959207830912500531)
    ·
      refine ⟨83378828938811746368750797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55585885959207830912500531 83378828938811746368750797)
      ·
        refine ⟨31267060852054404888281549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83378828938811746368750797 31267060852054404888281549)
        ·
          refine ⟨11725147819520401833105581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31267060852054404888281549 11725147819520401833105581)
          ·
            refine ⟨4396930432320150687414593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11725147819520401833105581 4396930432320150687414593)
            ·
              refine ⟨3297697824240113015560945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4396930432320150687414593 3297697824240113015560945)
              ·
                refine ⟨2473273368180084761670709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297697824240113015560945 2473273368180084761670709)
                ·
                  refine ⟨231869378266882946406629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2473273368180084761670709 231869378266882946406629)
                  ·
                    rfl

theorem cell23_4064076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_4064076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064076 prefixEnd_4064076 := by exact prefixLift 4064076
  have htrace : WordTrace (prefixWord ++ tailWord_4064076) baseStart_4064076 baseEnd_4064076 := by
    simpa [prefixWord, tailWord_4064076, baseEnd_4064076] using wordTrace_append hprefix tailTrace_4064076
  have hstable : (prefixWord ++ tailWord_4064076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064076).length < 2 ^ (prefixWord ++ tailWord_4064076).sum := by decide
  have hdescent : baseEnd_4064076 < baseStart_4064076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064136 : List Nat := [2, 1, 3, 3, 2, 1, 2, 4, 1, 4]
def baseStart_4064136 : Nat := 118140960795 + 4064136 * 2 ^ 59
def prefixEnd_4064136 : Nat := 4983230072969 + 3 ^ 40 * 4064136 * 2
def baseEnd_4064136 : Nat := 695618404413738760969795

theorem tailTrace_4064136 : CollatzResearch.WordTrace tailWord_4064136 prefixEnd_4064136 695618404413738760969795 := by
  unfold tailWord_4064136
  simp only [CollatzResearch.WordTrace]
  refine ⟨74115608802168423006926131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98820811736224564009234841 74115608802168423006926131)
  ·
    refine ⟨111173413203252634510389197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74115608802168423006926131 111173413203252634510389197)
    ·
      refine ⟨41690029951219737941395949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111173413203252634510389197 41690029951219737941395949)
      ·
        refine ⟨15633761231707401728023481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41690029951219737941395949 15633761231707401728023481)
        ·
          refine ⟨11725320923780551296017611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15633761231707401728023481 11725320923780551296017611)
          ·
            refine ⟨17587981385670826944026417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11725320923780551296017611 17587981385670826944026417)
            ·
              refine ⟨13190986039253120208019813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17587981385670826944026417 13190986039253120208019813)
              ·
                refine ⟨2473309882359960039003715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13190986039253120208019813 2473309882359960039003715)
                ·
                  refine ⟨3709964823539940058505573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473309882359960039003715 3709964823539940058505573)
                  ·
                    refine ⟨695618404413738760969795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3709964823539940058505573 695618404413738760969795)
                    ·
                      rfl

theorem cell23_4064136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_4064136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064136 prefixEnd_4064136 := by exact prefixLift 4064136
  have htrace : WordTrace (prefixWord ++ tailWord_4064136) baseStart_4064136 baseEnd_4064136 := by
    simpa [prefixWord, tailWord_4064136, baseEnd_4064136] using wordTrace_append hprefix tailTrace_4064136
  have hstable : (prefixWord ++ tailWord_4064136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064136).length < 2 ^ (prefixWord ++ tailWord_4064136).sum := by decide
  have hdescent : baseEnd_4064136 < baseStart_4064136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064149 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 6]
def baseStart_4064149 : Nat := 118140960795 + 4064149 * 2 ^ 59
def prefixEnd_4064149 : Nat := 4983230072969 + 3 ^ 40 * 4064149 * 2
def baseEnd_4064149 : Nat := 231873543165524970227425

theorem tailTrace_4064149 : CollatzResearch.WordTrace tailWord_4064149 prefixEnd_4064149 231873543165524970227425 := by
  unfold tailWord_4064149
  simp only [CollatzResearch.WordTrace]
  refine ⟨148231691753289749234075501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98821127835526499489383667 148231691753289749234075501)
  ·
    refine ⟨55586884407483655962778313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148231691753289749234075501 55586884407483655962778313)
    ·
      refine ⟨41690163305612741972083735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55586884407483655962778313 41690163305612741972083735)
      ·
        refine ⟨62535244958419112958125603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41690163305612741972083735 62535244958419112958125603)
        ·
          refine ⟨93802867437628669437188405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62535244958419112958125603 93802867437628669437188405)
          ·
            refine ⟨8794018822277687759736413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93802867437628669437188405 8794018822277687759736413)
            ·
              refine ⟨3297757058354132909901155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8794018822277687759736413 3297757058354132909901155)
              ·
                refine ⟨4946635587531199364851733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3297757058354132909901155 4946635587531199364851733)
                ·
                  refine ⟨231873543165524970227425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4946635587531199364851733 231873543165524970227425)
                  ·
                    rfl

theorem cell23_4064149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_4064149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064149 prefixEnd_4064149 := by exact prefixLift 4064149
  have htrace : WordTrace (prefixWord ++ tailWord_4064149) baseStart_4064149 baseEnd_4064149 := by
    simpa [prefixWord, tailWord_4064149, baseEnd_4064149] using wordTrace_append hprefix tailTrace_4064149
  have hstable : (prefixWord ++ tailWord_4064149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064149).length < 2 ^ (prefixWord ++ tailWord_4064149).sum := by decide
  have hdescent : baseEnd_4064149 < baseStart_4064149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064169 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 2, 3, 2]
def baseStart_4064169 : Nat := 118140960795 + 4064169 * 2 ^ 59
def prefixEnd_4064169 : Nat := 4983230072969 + 3 ^ 40 * 4064169 * 2
def baseEnd_4064169 : Nat := 2086872158102814653796733

theorem tailTrace_4064169 : CollatzResearch.WordTrace tailWord_4064169 prefixEnd_4064169 2086872158102814653796733 := by
  unfold tailWord_4064169
  simp only [CollatzResearch.WordTrace]
  refine ⟨148232421213217292649803561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98821614142144861766535707 148232421213217292649803561)
  ·
    refine ⟨111174315909912969487352671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148232421213217292649803561 111174315909912969487352671)
    ·
      refine ⟨166761473864869454231029007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111174315909912969487352671 166761473864869454231029007)
      ·
        refine ⟨250142210797304181346543511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166761473864869454231029007 250142210797304181346543511)
        ·
          refine ⟨375213316195956272019815267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250142210797304181346543511 375213316195956272019815267)
          ·
            refine ⟨562819974293934408029722901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375213316195956272019815267 562819974293934408029722901)
            ·
              refine ⟨26382186295028175376393261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 562819974293934408029722901 26382186295028175376393261)
              ·
                refine ⟨9893319860635565766147473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26382186295028175376393261 9893319860635565766147473)
                ·
                  refine ⟨7419989895476674324610605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9893319860635565766147473 7419989895476674324610605)
                  ·
                    refine ⟨2782496210803752871728977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7419989895476674324610605 2782496210803752871728977)
                    ·
                      refine ⟨2086872158102814653796733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782496210803752871728977 2086872158102814653796733)
                      ·
                        rfl

theorem cell23_4064169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 3, 2].length) (baseStart_4064169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064169 prefixEnd_4064169 := by exact prefixLift 4064169
  have htrace : WordTrace (prefixWord ++ tailWord_4064169) baseStart_4064169 baseEnd_4064169 := by
    simpa [prefixWord, tailWord_4064169, baseEnd_4064169] using wordTrace_append hprefix tailTrace_4064169
  have hstable : (prefixWord ++ tailWord_4064169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064169).length < 2 ^ (prefixWord ++ tailWord_4064169).sum := by decide
  have hdescent : baseEnd_4064169 < baseStart_4064169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064202 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_4064202 : Nat := 118140960795 + 4064202 * 2 ^ 59
def prefixEnd_4064202 : Nat := 4983230072969 + 3 ^ 40 * 4064202 * 2
def baseEnd_4064202 : Nat := 2086889102964413024684081

theorem tailTrace_4064202 : CollatzResearch.WordTrace tailWord_4064202 prefixEnd_4064202 2086889102964413024684081 := by
  unfold tailWord_4064202
  simp only [CollatzResearch.WordTrace]
  refine ⟨37058406205524434821438715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98822416548065159523836573 37058406205524434821438715)
  ·
    refine ⟨55587609308286652232158073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37058406205524434821438715 55587609308286652232158073)
    ·
      refine ⟨41690706981214989174118555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55587609308286652232158073 41690706981214989174118555)
      ·
        refine ⟨62536060471822483761177833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41690706981214989174118555 62536060471822483761177833)
        ·
          refine ⟨46902045353866862820883375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62536060471822483761177833 46902045353866862820883375)
          ·
            refine ⟨70353068030800294231325063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46902045353866862820883375 70353068030800294231325063)
            ·
              refine ⟨105529602046200441346987595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70353068030800294231325063 105529602046200441346987595)
              ·
                refine ⟨158294403069300662020481393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105529602046200441346987595 158294403069300662020481393)
                ·
                  refine ⟨118720802301975496515361045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158294403069300662020481393 118720802301975496515361045)
                  ·
                    refine ⟨5565037607905101399157549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118720802301975496515361045 5565037607905101399157549)
                    ·
                      refine ⟨2086889102964413024684081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5565037607905101399157549 2086889102964413024684081)
                      ·
                        rfl

theorem cell23_4064202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_4064202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064202 prefixEnd_4064202 := by exact prefixLift 4064202
  have htrace : WordTrace (prefixWord ++ tailWord_4064202) baseStart_4064202 baseEnd_4064202 := by
    simpa [prefixWord, tailWord_4064202, baseEnd_4064202] using wordTrace_append hprefix tailTrace_4064202
  have hstable : (prefixWord ++ tailWord_4064202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064202).length < 2 ^ (prefixWord ++ tailWord_4064202).sum := by decide
  have hdescent : baseEnd_4064202 < baseStart_4064202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064209 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 2, 4]
def baseStart_4064209 : Nat := 118140960795 + 4064209 * 2 ^ 59
def prefixEnd_4064209 : Nat := 4983230072969 + 3 ^ 40 * 4064209 * 2
def baseEnd_4064209 : Nat := 695630899109664832432183

theorem tailTrace_4064209 : CollatzResearch.WordTrace tailWord_4064209 prefixEnd_4064209 695630899109664832432183 := by
  unfold tailWord_4064209
  simp only [CollatzResearch.WordTrace]
  refine ⟨148233880133072379481259681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98822586755381586320839787 148233880133072379481259681)
  ·
    refine ⟨111175410099804284610944761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148233880133072379481259681 111175410099804284610944761)
    ·
      refine ⟨83381557574853213458208571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111175410099804284610944761 83381557574853213458208571)
      ·
        refine ⟨125072336362279820187312857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83381557574853213458208571 125072336362279820187312857)
        ·
          refine ⟨93804252271709865140484643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125072336362279820187312857 93804252271709865140484643)
          ·
            refine ⟨140706378407564797710726965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93804252271709865140484643 140706378407564797710726965)
            ·
              refine ⟨13191222975709199785380653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140706378407564797710726965 13191222975709199785380653)
              ·
                refine ⟨4946708615890949919517745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13191222975709199785380653 4946708615890949919517745)
                ·
                  refine ⟨3710031461918212439638309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4946708615890949919517745 3710031461918212439638309)
                  ·
                    refine ⟨695630899109664832432183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3710031461918212439638309 695630899109664832432183)
                    ·
                      rfl

theorem cell23_4064209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_4064209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064209 prefixEnd_4064209 := by exact prefixLift 4064209
  have htrace : WordTrace (prefixWord ++ tailWord_4064209) baseStart_4064209 baseEnd_4064209 := by
    simpa [prefixWord, tailWord_4064209, baseEnd_4064209] using wordTrace_append hprefix tailTrace_4064209
  have hstable : (prefixWord ++ tailWord_4064209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064209).length < 2 ^ (prefixWord ++ tailWord_4064209).sum := by decide
  have hdescent : baseEnd_4064209 < baseStart_4064209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064213 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_4064213 : Nat := 118140960795 + 4064213 * 2 ^ 59
def prefixEnd_4064213 : Nat := 4983230072969 + 3 ^ 40 * 4064213 * 2
def baseEnd_4064213 : Nat := 695631583750537493882177

theorem tailTrace_4064213 : CollatzResearch.WordTrace tailWord_4064213 prefixEnd_4064213 695631583750537493882177 := by
  unfold tailWord_4064213
  simp only [CollatzResearch.WordTrace]
  refine ⟨148234026025057888164405293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98822684016705258776270195 148234026025057888164405293)
  ·
    refine ⟨55587759759396708061651985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148234026025057888164405293 55587759759396708061651985)
    ·
      refine ⟨41690819819547531046238989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55587759759396708061651985 41690819819547531046238989)
      ·
        refine ⟨15634057432330324142339621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41690819819547531046238989 15634057432330324142339621)
        ·
          refine ⟨2931385768561935776688679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15634057432330324142339621 2931385768561935776688679)
          ·
            refine ⟨4397078652842903665033019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931385768561935776688679 4397078652842903665033019)
            ·
              refine ⟨6595617979264355497549529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397078652842903665033019 6595617979264355497549529)
              ·
                refine ⟨4946713484448266623162147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6595617979264355497549529 4946713484448266623162147)
                ·
                  refine ⟨7420070226672399934743221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946713484448266623162147 7420070226672399934743221)
                  ·
                    refine ⟨695631583750537493882177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7420070226672399934743221 695631583750537493882177)
                    ·
                      rfl

theorem cell23_4064213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_4064213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064213 prefixEnd_4064213 := by exact prefixLift 4064213
  have htrace : WordTrace (prefixWord ++ tailWord_4064213) baseStart_4064213 baseEnd_4064213 := by
    simpa [prefixWord, tailWord_4064213, baseEnd_4064213] using wordTrace_append hprefix tailTrace_4064213
  have hstable : (prefixWord ++ tailWord_4064213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064213).length < 2 ^ (prefixWord ++ tailWord_4064213).sum := by decide
  have hdescent : baseEnd_4064213 < baseStart_4064213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064216 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 1, 1, 4]
def baseStart_4064216 : Nat := 118140960795 + 4064216 * 2 ^ 59
def prefixEnd_4064216 : Nat := 4983230072969 + 3 ^ 40 * 4064216 * 2
def baseEnd_4064216 : Nat := 2086896291693575969909017

theorem tailTrace_4064216 : CollatzResearch.WordTrace tailWord_4064216 prefixEnd_4064216 2086896291693575969909017 := by
  unfold tailWord_4064216
  simp only [CollatzResearch.WordTrace]
  refine ⟨74117067722023509838382251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98822756962698013117843001 74117067722023509838382251)
  ·
    refine ⟨111175601583035264757573377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74117067722023509838382251 111175601583035264757573377)
    ·
      refine ⟨83381701187276448568180033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111175601583035264757573377 83381701187276448568180033)
      ·
        refine ⟨62536275890457336426135025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83381701187276448568180033 62536275890457336426135025)
        ·
          refine ⟨46902206917843002319601269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62536275890457336426135025 46902206917843002319601269)
          ·
            refine ⟨4397081898547781467462619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46902206917843002319601269 4397081898547781467462619)
            ·
              refine ⟨6595622847821672201193929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397081898547781467462619 6595622847821672201193929)
              ·
                refine ⟨4946717135866254150895447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6595622847821672201193929 4946717135866254150895447)
                ·
                  refine ⟨7420075703799381226343171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946717135866254150895447 7420075703799381226343171)
                  ·
                    refine ⟨11130113555699071839514757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7420075703799381226343171 11130113555699071839514757)
                    ·
                      refine ⟨2086896291693575969909017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11130113555699071839514757 2086896291693575969909017)
                      ·
                        rfl

theorem cell23_4064216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_4064216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064216 prefixEnd_4064216 := by exact prefixLift 4064216
  have htrace : WordTrace (prefixWord ++ tailWord_4064216) baseStart_4064216 baseEnd_4064216 := by
    simpa [prefixWord, tailWord_4064216, baseEnd_4064216] using wordTrace_append hprefix tailTrace_4064216
  have hstable : (prefixWord ++ tailWord_4064216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064216).length < 2 ^ (prefixWord ++ tailWord_4064216).sum := by decide
  have hdescent : baseEnd_4064216 < baseStart_4064216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064226 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4064226 : Nat := 118140960795 + 4064226 * 2 ^ 59
def prefixEnd_4064226 : Nat := 4983230072969 + 3 ^ 40 * 4064226 * 2
def baseEnd_4064226 : Nat := 695633808833373643594657

theorem tailTrace_4064226 : CollatzResearch.WordTrace tailWord_4064226 prefixEnd_4064226 695633808833373643594657 := by
  unfold tailWord_4064226
  simp only [CollatzResearch.WordTrace]
  refine ⟨37058625043502697846157133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98823000116007194256419021 37058625043502697846157133)
  ·
    refine ⟨13896984391313511692308925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37058625043502697846157133 13896984391313511692308925)
    ·
      refine ⟨5211369146742566884615847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13896984391313511692308925 5211369146742566884615847)
      ·
        refine ⟨7817053720113850326923771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211369146742566884615847 7817053720113850326923771)
        ·
          refine ⟨11725580580170775490385657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817053720113850326923771 11725580580170775490385657)
          ·
            refine ⟨8794185435128081617789243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11725580580170775490385657 8794185435128081617789243)
            ·
              refine ⟨13191278152692122426683865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794185435128081617789243 13191278152692122426683865)
              ·
                refine ⟨9893458614519091820012899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13191278152692122426683865 9893458614519091820012899)
                ·
                  refine ⟨14840187921778637730019349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9893458614519091820012899 14840187921778637730019349)
                  ·
                    refine ⟨695633808833373643594657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14840187921778637730019349 695633808833373643594657)
                    ·
                      rfl

theorem cell23_4064226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4064226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064226 prefixEnd_4064226 := by exact prefixLift 4064226
  have htrace : WordTrace (prefixWord ++ tailWord_4064226) baseStart_4064226 baseEnd_4064226 := by
    simpa [prefixWord, tailWord_4064226, baseEnd_4064226] using wordTrace_append hprefix tailTrace_4064226
  have hstable : (prefixWord ++ tailWord_4064226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064226).length < 2 ^ (prefixWord ++ tailWord_4064226).sum := by decide
  have hdescent : baseEnd_4064226 < baseStart_4064226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064252 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_4064252 : Nat := 118140960795 + 4064252 * 2 ^ 59
def prefixEnd_4064252 : Nat := 4983230072969 + 3 ^ 40 * 4064252 * 2
def baseEnd_4064252 : Nat := 695638258999045943019617

theorem tailTrace_4064252 : CollatzResearch.WordTrace tailWord_4064252 prefixEnd_4064252 695638258999045943019617 := by
  unfold tailWord_4064252
  simp only [CollatzResearch.WordTrace]
  refine ⟨74117724235958298912537505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98823632314611065216716673 74117724235958298912537505)
  ·
    refine ⟨55588293176968724184403129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74117724235958298912537505 55588293176968724184403129)
    ·
      refine ⟨41691219882726543138302347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55588293176968724184403129 41691219882726543138302347)
      ·
        refine ⟨62536829824089814707453521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41691219882726543138302347 62536829824089814707453521)
        ·
          refine ⟨46902622368067361030590141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62536829824089814707453521 46902622368067361030590141)
          ·
            refine ⟨17588483388025260386471303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46902622368067361030590141 17588483388025260386471303)
            ·
              refine ⟨26382725082037890579706955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17588483388025260386471303 26382725082037890579706955)
              ·
                refine ⟨39574087623056835869560433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26382725082037890579706955 39574087623056835869560433)
                ·
                  refine ⟨29680565717292626902170325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39574087623056835869560433 29680565717292626902170325)
                  ·
                    refine ⟨695638258999045943019617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29680565717292626902170325 695638258999045943019617)
                    ·
                      rfl

theorem cell23_4064252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_4064252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064252 prefixEnd_4064252 := by exact prefixLift 4064252
  have htrace : WordTrace (prefixWord ++ tailWord_4064252) baseStart_4064252 baseEnd_4064252 := by
    simpa [prefixWord, tailWord_4064252, baseEnd_4064252] using wordTrace_append hprefix tailTrace_4064252
  have hstable : (prefixWord ++ tailWord_4064252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064252).length < 2 ^ (prefixWord ++ tailWord_4064252).sum := by decide
  have hdescent : baseEnd_4064252 < baseStart_4064252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064266 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_4064266 : Nat := 118140960795 + 4064266 * 2 ^ 59
def prefixEnd_4064266 : Nat := 4983230072969 + 3 ^ 40 * 4064266 * 2
def baseEnd_4064266 : Nat := 2086921965726300774283787

theorem tailTrace_4064266 : CollatzResearch.WordTrace tailWord_4064266 prefixEnd_4064266 2086921965726300774283787 := by
  unfold tailWord_4064266
  simp only [CollatzResearch.WordTrace]
  refine ⟨37058989773466469554021163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98823972729243918810723101 37058989773466469554021163)
  ·
    refine ⟨55588484660199704331031745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37058989773466469554021163 55588484660199704331031745)
    ·
      refine ⟨41691363495149778248273809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55588484660199704331031745 41691363495149778248273809)
      ·
        refine ⟨31268522621362333686205357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41691363495149778248273809 31268522621362333686205357)
        ·
          refine ⟨11725695983010875132327009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31268522621362333686205357 11725695983010875132327009)
          ·
            refine ⟨8794271987258156349245257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11725695983010875132327009 8794271987258156349245257)
            ·
              refine ⟨6595703990443617261933943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8794271987258156349245257 6595703990443617261933943)
              ·
                refine ⟨9893555985665425892900915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6595703990443617261933943 9893555985665425892900915)
                ·
                  refine ⟨14840333978498138839351373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9893555985665425892900915 14840333978498138839351373)
                  ·
                    refine ⟨5565125241936802064756765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14840333978498138839351373 5565125241936802064756765)
                    ·
                      refine ⟨2086921965726300774283787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5565125241936802064756765 2086921965726300774283787)
                      ·
                        rfl

theorem cell23_4064266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_4064266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064266 prefixEnd_4064266 := by exact prefixLift 4064266
  have htrace : WordTrace (prefixWord ++ tailWord_4064266) baseStart_4064266 baseEnd_4064266 := by
    simpa [prefixWord, tailWord_4064266, baseEnd_4064266] using wordTrace_append hprefix tailTrace_4064266
  have hstable : (prefixWord ++ tailWord_4064266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064266).length < 2 ^ (prefixWord ++ tailWord_4064266).sum := by decide
  have hdescent : baseEnd_4064266 < baseStart_4064266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064282 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_4064282 : Nat := 118140960795 + 4064282 * 2 ^ 59
def prefixEnd_4064282 : Nat := 4983230072969 + 3 ^ 40 * 4064282 * 2
def baseEnd_4064282 : Nat := 695643393805590903894571

theorem tailTrace_4064282 : CollatzResearch.WordTrace tailWord_4064282 prefixEnd_4064282 695643393805590903894571 := by
  unfold tailWord_4064282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37059135665451978237166775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98824361774538608632444733 37059135665451978237166775)
  ·
    refine ⟨55588703498177967355750163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37059135665451978237166775 55588703498177967355750163)
    ·
      refine ⟨83383055247266951033625245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55588703498177967355750163 83383055247266951033625245)
      ·
        refine ⟨31268645717725106637609467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83383055247266951033625245 31268645717725106637609467)
        ·
          refine ⟨46902968576587659956414201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31268645717725106637609467 46902968576587659956414201)
          ·
            refine ⟨35177226432440744967310651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46902968576587659956414201 35177226432440744967310651)
            ·
              refine ⟨52765839648661117450965977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35177226432440744967310651 52765839648661117450965977)
              ·
                refine ⟨39574379736495838088224483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52765839648661117450965977 39574379736495838088224483)
                ·
                  refine ⟨59361569604743757132336725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39574379736495838088224483 59361569604743757132336725)
                  ·
                    refine ⟨695643393805590903894571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59361569604743757132336725 695643393805590903894571)
                    ·
                      rfl

theorem cell23_4064282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_4064282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064282 prefixEnd_4064282 := by exact prefixLift 4064282
  have htrace : WordTrace (prefixWord ++ tailWord_4064282) baseStart_4064282 baseEnd_4064282 := by
    simpa [prefixWord, tailWord_4064282, baseEnd_4064282] using wordTrace_append hprefix tailTrace_4064282
  have hstable : (prefixWord ++ tailWord_4064282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064282).length < 2 ^ (prefixWord ++ tailWord_4064282).sum := by decide
  have hdescent : baseEnd_4064282 < baseStart_4064282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064359 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 4, 5]
def baseStart_4064359 : Nat := 118140960795 + 4064359 * 2 ^ 59
def prefixEnd_4064359 : Nat := 4983230072969 + 3 ^ 40 * 4064359 * 2
def baseEnd_4064359 : Nat := 695656573142389636806953

theorem tailTrace_4064359 : CollatzResearch.WordTrace tailWord_4064359 prefixEnd_4064359 695656573142389636806953 := by
  unfold tailWord_4064359
  simp only [CollatzResearch.WordTrace]
  refine ⟨148239351082528955099220131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98826234055019303399480087 148239351082528955099220131)
  ·
    refine ⟨222359026623793432648830197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148239351082528955099220131 222359026623793432648830197)
    ·
      refine ⟨20846158745980634310827831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222359026623793432648830197 20846158745980634310827831)
      ·
        refine ⟨31269238118970951466241747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20846158745980634310827831 31269238118970951466241747)
        ·
          refine ⟨46903857178456427199362621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31269238118970951466241747 46903857178456427199362621)
          ·
            refine ⟨17588946441921160199760983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46903857178456427199362621 17588946441921160199760983)
            ·
              refine ⟨26383419662881740299641475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17588946441921160199760983 26383419662881740299641475)
              ·
                refine ⟨39575129494322610449462213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26383419662881740299641475 39575129494322610449462213)
                ·
                  refine ⟨7420336780185489459274165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39575129494322610449462213 7420336780185489459274165)
                  ·
                    refine ⟨695656573142389636806953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7420336780185489459274165 695656573142389636806953)
                    ·
                      rfl

theorem cell23_4064359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_4064359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064359 prefixEnd_4064359 := by exact prefixLift 4064359
  have htrace : WordTrace (prefixWord ++ tailWord_4064359) baseStart_4064359 baseEnd_4064359 := by
    simpa [prefixWord, tailWord_4064359, baseEnd_4064359] using wordTrace_append hprefix tailTrace_4064359
  have hstable : (prefixWord ++ tailWord_4064359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064359).length < 2 ^ (prefixWord ++ tailWord_4064359).sum := by decide
  have hdescent : baseEnd_4064359 < baseStart_4064359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064416 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 3]
def baseStart_4064416 : Nat := 118140960795 + 4064416 * 2 ^ 59
def prefixEnd_4064416 : Nat := 4983230072969 + 3 ^ 40 * 4064416 * 2
def baseEnd_4064416 : Nat := 2086998987824475187408097

theorem tailTrace_4064416 : CollatzResearch.WordTrace tailWord_4064416 prefixEnd_4064416 2086998987824475187408097 := by
  unfold tailWord_4064416
  simp only [CollatzResearch.WordTrace]
  refine ⟨74120715021661226917022551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98827620028881635889363401 74120715021661226917022551)
  ·
    refine ⟨111181072532491840375533827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74120715021661226917022551 111181072532491840375533827)
    ·
      refine ⟨166771608798737760563300741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111181072532491840375533827 166771608798737760563300741)
      ·
        refine ⟨31269676649763330105618889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166771608798737760563300741 31269676649763330105618889)
        ·
          refine ⟨23452257487322497579214167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31269676649763330105618889 23452257487322497579214167)
          ·
            refine ⟨35178386230983746368821251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23452257487322497579214167 35178386230983746368821251)
            ·
              refine ⟨52767579346475619553231877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35178386230983746368821251 52767579346475619553231877)
              ·
                refine ⟨9893921127464178666230977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52767579346475619553231877 9893921127464178666230977)
                ·
                  refine ⟨7420440845598133999673233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9893921127464178666230977 7420440845598133999673233)
                  ·
                    refine ⟨5565330634198600499754925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420440845598133999673233 5565330634198600499754925)
                    ·
                      refine ⟨2086998987824475187408097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5565330634198600499754925 2086998987824475187408097)
                      ·
                        rfl

theorem cell23_4064416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_4064416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064416 prefixEnd_4064416 := by exact prefixLift 4064416
  have htrace : WordTrace (prefixWord ++ tailWord_4064416) baseStart_4064416 baseEnd_4064416 := by
    simpa [prefixWord, tailWord_4064416, baseEnd_4064416] using wordTrace_append hprefix tailTrace_4064416
  have hstable : (prefixWord ++ tailWord_4064416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064416).length < 2 ^ (prefixWord ++ tailWord_4064416).sum := by decide
  have hdescent : baseEnd_4064416 < baseStart_4064416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064479 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 3, 6]
def baseStart_4064479 : Nat := 118140960795 + 4064479 * 2 ^ 59
def prefixEnd_4064479 : Nat := 4983230072969 + 3 ^ 40 * 4064479 * 2
def baseEnd_4064479 : Nat := 695677112368569480306769

theorem tailTrace_4064479 : CollatzResearch.WordTrace tailWord_4064479 prefixEnd_4064479 695677112368569480306769 := by
  unfold tailWord_4064479
  simp only [CollatzResearch.WordTrace]
  refine ⟨148243727842094215593588491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98829151894729477062392327 148243727842094215593588491)
  ·
    refine ⟨222365591763141323390382737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148243727842094215593588491 222365591763141323390382737)
    ·
      refine ⟨166774193822355992542787053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222365591763141323390382737 166774193822355992542787053)
      ·
        refine ⟨62540322683383497203545145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166774193822355992542787053 62540322683383497203545145)
        ·
          refine ⟨46905242012537622902658859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62540322683383497203545145 46905242012537622902658859)
          ·
            refine ⟨70357863018806434353988289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46905242012537622902658859 70357863018806434353988289)
            ·
              refine ⟨52768397264104825765491217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70357863018806434353988289 52768397264104825765491217)
              ·
                refine ⟨39576297948078619324118413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52768397264104825765491217 39576297948078619324118413)
                ·
                  refine ⟨14841111730529482246544405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39576297948078619324118413 14841111730529482246544405)
                  ·
                    refine ⟨695677112368569480306769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14841111730529482246544405 695677112368569480306769)
                    ·
                      rfl

theorem cell23_4064479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_4064479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064479 prefixEnd_4064479 := by exact prefixLift 4064479
  have htrace : WordTrace (prefixWord ++ tailWord_4064479) baseStart_4064479 baseEnd_4064479 := by
    simpa [prefixWord, tailWord_4064479, baseEnd_4064479] using wordTrace_append hprefix tailTrace_4064479
  have hstable : (prefixWord ++ tailWord_4064479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064479).length < 2 ^ (prefixWord ++ tailWord_4064479).sum := by decide
  have hdescent : baseEnd_4064479 < baseStart_4064479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064480 : List Nat := [2, 1, 1, 3, 1, 4, 2, 4, 1, 1, 3]
def baseStart_4064480 : Nat := 118140960795 + 4064480 * 2 ^ 59
def prefixEnd_4064480 : Nat := 4983230072969 + 3 ^ 40 * 4064480 * 2
def baseEnd_4064480 : Nat := 2087031850586362937007803

theorem tailTrace_4064480 : CollatzResearch.WordTrace tailWord_4064480 prefixEnd_4064480 2087031850586362937007803 := by
  unfold tailWord_4064480
  simp only [CollatzResearch.WordTrace]
  refine ⟨74121882157545296382187447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98829176210060395176249929 74121882157545296382187447)
  ·
    refine ⟨111182823236317944573281171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74121882157545296382187447 111182823236317944573281171)
    ·
      refine ⟨166774234854476916859921757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111182823236317944573281171 166774234854476916859921757)
      ·
        refine ⟨62540338070428843822470659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166774234854476916859921757 62540338070428843822470659)
        ·
          refine ⟨93810507105643265733705989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62540338070428843822470659 93810507105643265733705989)
          ·
            refine ⟨17589470082308112325069873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93810507105643265733705989 17589470082308112325069873)
            ·
              refine ⟨13192102561731084243802405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17589470082308112325069873 13192102561731084243802405)
              ·
                refine ⟨2473519230324578295712951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13192102561731084243802405 2473519230324578295712951)
                ·
                  refine ⟨3710278845486867443569427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473519230324578295712951 3710278845486867443569427)
                  ·
                    refine ⟨5565418268230301165354141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3710278845486867443569427 5565418268230301165354141)
                    ·
                      refine ⟨2087031850586362937007803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5565418268230301165354141 2087031850586362937007803)
                      ·
                        rfl

theorem cell23_4064480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_4064480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064480 prefixEnd_4064480 := by exact prefixLift 4064480
  have htrace : WordTrace (prefixWord ++ tailWord_4064480) baseStart_4064480 baseEnd_4064480 := by
    simpa [prefixWord, tailWord_4064480, baseEnd_4064480] using wordTrace_append hprefix tailTrace_4064480
  have hstable : (prefixWord ++ tailWord_4064480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064480).length < 2 ^ (prefixWord ++ tailWord_4064480).sum := by decide
  have hdescent : baseEnd_4064480 < baseStart_4064480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064523 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 3]
def baseStart_4064523 : Nat := 118140960795 + 4064523 * 2 ^ 59
def prefixEnd_4064523 : Nat := 4983230072969 + 3 ^ 40 * 4064523 * 2
def baseEnd_4064523 : Nat := 2087053930254506268770105

theorem tailTrace_4064523 : CollatzResearch.WordTrace tailWord_4064523 prefixEnd_4064523 2087053930254506268770105 := by
  unfold tailWord_4064523
  simp only [CollatzResearch.WordTrace]
  refine ⟨148245332653934811108190223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98830221769289874072126815 148245332653934811108190223)
  ·
    refine ⟨222367998980902216662285335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148245332653934811108190223 222367998980902216662285335)
    ·
      refine ⟨333551998471353324993428003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222367998980902216662285335 333551998471353324993428003)
      ·
        refine ⟨500327997707029987490142005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333551998471353324993428003 500327997707029987490142005)
        ·
          refine ⟨46905749785034061327200813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 500327997707029987490142005 46905749785034061327200813)
          ·
            refine ⟨17589656169387772997700305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46905749785034061327200813 17589656169387772997700305)
            ·
              refine ⟨13192242127040829748275229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17589656169387772997700305 13192242127040829748275229)
              ·
                refine ⟨4947090797640311155603211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13192242127040829748275229 4947090797640311155603211)
                ·
                  refine ⟨7420636196460466733404817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947090797640311155603211 7420636196460466733404817)
                  ·
                    refine ⟨5565477147345350050053613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420636196460466733404817 5565477147345350050053613)
                    ·
                      refine ⟨2087053930254506268770105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5565477147345350050053613 2087053930254506268770105)
                      ·
                        rfl

theorem cell23_4064523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 3].length) (baseStart_4064523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064523 prefixEnd_4064523 := by exact prefixLift 4064523
  have htrace : WordTrace (prefixWord ++ tailWord_4064523) baseStart_4064523 baseEnd_4064523 := by
    simpa [prefixWord, tailWord_4064523, baseEnd_4064523] using wordTrace_append hprefix tailTrace_4064523
  have hstable : (prefixWord ++ tailWord_4064523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064523).length < 2 ^ (prefixWord ++ tailWord_4064523).sum := by decide
  have hdescent : baseEnd_4064523 < baseStart_4064523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064526 : List Nat := [4, 1, 1, 2, 1, 5, 9]
def baseStart_4064526 : Nat := 118140960795 + 4064526 * 2 ^ 59
def prefixEnd_4064526 : Nat := 4983230072969 + 3 ^ 40 * 4064526 * 2
def baseEnd_4064526 : Nat := 25766116922178638975711

theorem tailTrace_4064526 : CollatzResearch.WordTrace tailWord_4064526 prefixEnd_4064526 25766116922178638975711 := by
  unfold tailWord_4064526
  simp only [CollatzResearch.WordTrace]
  refine ⟨18530680259115492827568679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98830294715282628413699621 18530680259115492827568679)
  ·
    refine ⟨27796020388673239241353019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18530680259115492827568679 27796020388673239241353019)
    ·
      refine ⟨41694030583009858862029529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27796020388673239241353019 41694030583009858862029529)
      ·
        refine ⟨31270522937257394146522147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41694030583009858862029529 31270522937257394146522147)
        ·
          refine ⟨46905784405886091219783221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31270522937257394146522147 46905784405886091219783221)
          ·
            refine ⟨4397417288051821051854677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46905784405886091219783221 4397417288051821051854677)
            ·
              refine ⟨25766116922178638975711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4397417288051821051854677 25766116922178638975711)
              ·
                rfl

theorem cell23_4064526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 9].length) (baseStart_4064526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064526 prefixEnd_4064526 := by exact prefixLift 4064526
  have htrace : WordTrace (prefixWord ++ tailWord_4064526) baseStart_4064526 baseEnd_4064526 := by
    simpa [prefixWord, tailWord_4064526, baseEnd_4064526] using wordTrace_append hprefix tailTrace_4064526
  have hstable : (prefixWord ++ tailWord_4064526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064526).length < 2 ^ (prefixWord ++ tailWord_4064526).sum := by decide
  have hdescent : baseEnd_4064526 < baseStart_4064526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064539 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 2, 7]
def baseStart_4064539 : Nat := 118140960795 + 4064539 * 2 ^ 59
def prefixEnd_4064539 : Nat := 4983230072969 + 3 ^ 40 * 4064539 * 2
def baseEnd_4064539 : Nat := 695687381981659402056677

theorem tailTrace_4064539 : CollatzResearch.WordTrace tailWord_4064539 prefixEnd_4064539 695687381981659402056677 := by
  unfold tailWord_4064539
  simp only [CollatzResearch.WordTrace]
  refine ⟨148245916221876845840772671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98830610814584563893848447 148245916221876845840772671)
  ·
    refine ⟨222368874332815268761159007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148245916221876845840772671 222368874332815268761159007)
    ·
      refine ⟨333553311499222903141738511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222368874332815268761159007 333553311499222903141738511)
      ·
        refine ⟨500329967248834354712607767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333553311499222903141738511 500329967248834354712607767)
        ·
          refine ⟨750494950873251532068911651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500329967248834354712607767 750494950873251532068911651)
          ·
            refine ⟨1125742426309877298103367477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750494950873251532068911651 1125742426309877298103367477)
            ·
              refine ⟨105538352466550996697190701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1125742426309877298103367477 105538352466550996697190701)
              ·
                refine ⟨39576882174956623761446513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105538352466550996697190701 39576882174956623761446513)
                ·
                  refine ⟨29682661631217467821084885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39576882174956623761446513 29682661631217467821084885)
                  ·
                    refine ⟨695687381981659402056677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29682661631217467821084885 695687381981659402056677)
                    ·
                      rfl

theorem cell23_4064539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 7].length) (baseStart_4064539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064539 prefixEnd_4064539 := by exact prefixLift 4064539
  have htrace : WordTrace (prefixWord ++ tailWord_4064539) baseStart_4064539 baseEnd_4064539 := by
    simpa [prefixWord, tailWord_4064539, baseEnd_4064539] using wordTrace_append hprefix tailTrace_4064539
  have hstable : (prefixWord ++ tailWord_4064539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064539).length < 2 ^ (prefixWord ++ tailWord_4064539).sum := by decide
  have hdescent : baseEnd_4064539 < baseStart_4064539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064557 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4064557 : Nat := 118140960795 + 4064557 * 2 ^ 59
def prefixEnd_4064557 : Nat := 4983230072969 + 3 ^ 40 * 4064557 * 2
def baseEnd_4064557 : Nat := 2087071388596759135744949

theorem tailTrace_4064557 : CollatzResearch.WordTrace tailWord_4064557 prefixEnd_4064557 2087071388596759135744949 := by
  unfold tailWord_4064557
  simp only [CollatzResearch.WordTrace]
  refine ⟨148246572735811634914927925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98831048490541089943285283 148246572735811634914927925)
  ·
    refine ⟨13898116193982340773274493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148246572735811634914927925 13898116193982340773274493)
    ·
      refine ⟨5211793572743377789977935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13898116193982340773274493 5211793572743377789977935)
      ·
        refine ⟨7817690359115066684966903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211793572743377789977935 7817690359115066684966903)
        ·
          refine ⟨11726535538672600027450355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817690359115066684966903 11726535538672600027450355)
          ·
            refine ⟨17589803308008900041175533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11726535538672600027450355 17589803308008900041175533)
            ·
              refine ⟨6596176240503337515440825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17589803308008900041175533 6596176240503337515440825)
              ·
                refine ⟨4947132180377503136580619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6596176240503337515440825 4947132180377503136580619)
                ·
                  refine ⟨7420698270566254704870929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947132180377503136580619 7420698270566254704870929)
                  ·
                    refine ⟨5565523702924691028653197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7420698270566254704870929 5565523702924691028653197)
                    ·
                      refine ⟨2087071388596759135744949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5565523702924691028653197 2087071388596759135744949)
                      ·
                        rfl

theorem cell23_4064557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4064557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064557 prefixEnd_4064557 := by exact prefixLift 4064557
  have htrace : WordTrace (prefixWord ++ tailWord_4064557) baseStart_4064557 baseEnd_4064557 := by
    simpa [prefixWord, tailWord_4064557, baseEnd_4064557] using wordTrace_append hprefix tailTrace_4064557
  have hstable : (prefixWord ++ tailWord_4064557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064557).length < 2 ^ (prefixWord ++ tailWord_4064557).sum := by decide
  have hdescent : baseEnd_4064557 < baseStart_4064557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064559 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_4064559 : Nat := 118140960795 + 4064559 * 2 ^ 59
def prefixEnd_4064559 : Nat := 4983230072969 + 3 ^ 40 * 4064559 * 2
def baseEnd_4064559 : Nat := 2087072415558068127919939

theorem tailTrace_4064559 : CollatzResearch.WordTrace tailWord_4064559 prefixEnd_4064559 2087072415558068127919939 := by
  unfold tailWord_4064559
  simp only [CollatzResearch.WordTrace]
  refine ⟨148246645681804389256500731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98831097121202926171000487 148246645681804389256500731)
  ·
    refine ⟨222369968522706583884751097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148246645681804389256500731 222369968522706583884751097)
    ·
      refine ⟨166777476392029937913563323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222369968522706583884751097 166777476392029937913563323)
      ·
        refine ⟨250166214588044906870344985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166777476392029937913563323 250166214588044906870344985)
        ·
          refine ⟨187624660941033680152758739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250166214588044906870344985 187624660941033680152758739)
          ·
            refine ⟨281436991411550520229138109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187624660941033680152758739 281436991411550520229138109)
            ·
              refine ⟨105538871779331445085926791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281436991411550520229138109 105538871779331445085926791)
              ·
                refine ⟨158308307668997167628890187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105538871779331445085926791 158308307668997167628890187)
                ·
                  refine ⟨237462461503495751443335281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158308307668997167628890187 237462461503495751443335281)
                  ·
                    refine ⟨178096846127621813582501461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237462461503495751443335281 178096846127621813582501461)
                    ·
                      refine ⟨2087072415558068127919939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 178096846127621813582501461 2087072415558068127919939)
                      ·
                        rfl

theorem cell23_4064559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_4064559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064559 prefixEnd_4064559 := by exact prefixLift 4064559
  have htrace : WordTrace (prefixWord ++ tailWord_4064559) baseStart_4064559 baseEnd_4064559 := by
    simpa [prefixWord, tailWord_4064559, baseEnd_4064559] using wordTrace_append hprefix tailTrace_4064559
  have hstable : (prefixWord ++ tailWord_4064559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064559).length < 2 ^ (prefixWord ++ tailWord_4064559).sum := by decide
  have hdescent : baseEnd_4064559 < baseStart_4064559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064593 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 3, 4, 2]
def baseStart_4064593 : Nat := 118140960795 + 4064593 * 2 ^ 59
def prefixEnd_4064593 : Nat := 4983230072969 + 3 ^ 40 * 4064593 * 2
def baseEnd_4064593 : Nat := 2087089873900320994894783

theorem tailTrace_4064593 : CollatzResearch.WordTrace tailWord_4064593 prefixEnd_4064593 2087089873900320994894783 := by
  unfold tailWord_4064593
  simp only [CollatzResearch.WordTrace]
  refine ⟨148247885763681213063238433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98831923842454142042158955 148247885763681213063238433)
  ·
    refine ⟨111185914322760909797428825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148247885763681213063238433 111185914322760909797428825)
    ·
      refine ⟨83389435742070682348071619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111185914322760909797428825 83389435742070682348071619)
      ·
        refine ⟨125084153613106023522107429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83389435742070682348071619 125084153613106023522107429)
        ·
          refine ⟨23453278802457379410395143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125084153613106023522107429 23453278802457379410395143)
          ·
            refine ⟨35179918203686069115592715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23453278802457379410395143 35179918203686069115592715)
            ·
              refine ⟨52769877305529103673389073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35179918203686069115592715 52769877305529103673389073)
              ·
                refine ⟨39577407979146827755041805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52769877305529103673389073 39577407979146827755041805)
                ·
                  refine ⟨14841527992180060408140677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39577407979146827755041805 14841527992180060408140677)
                  ·
                    refine ⟨2782786498533761326526377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14841527992180060408140677 2782786498533761326526377)
                    ·
                      refine ⟨2087089873900320994894783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782786498533761326526377 2087089873900320994894783)
                      ·
                        rfl

theorem cell23_4064593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_4064593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064593 prefixEnd_4064593 := by exact prefixLift 4064593
  have htrace : WordTrace (prefixWord ++ tailWord_4064593) baseStart_4064593 baseEnd_4064593 := by
    simpa [prefixWord, tailWord_4064593, baseEnd_4064593] using wordTrace_append hprefix tailTrace_4064593
  have hstable : (prefixWord ++ tailWord_4064593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064593).length < 2 ^ (prefixWord ++ tailWord_4064593).sum := by decide
  have hdescent : baseEnd_4064593 < baseStart_4064593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064633 : List Nat := [1, 2, 1, 3, 2, 1, 3, 5, 5]
def baseStart_4064633 : Nat := 118140960795 + 4064633 * 2 ^ 59
def prefixEnd_4064633 : Nat := 4983230072969 + 3 ^ 40 * 4064633 * 2
def baseEnd_4064633 : Nat := 231901157014055648710511

theorem tailTrace_4064633 : CollatzResearch.WordTrace tailWord_4064633 prefixEnd_4064633 231901157014055648710511 := by
  unfold tailWord_4064633
  simp only [CollatzResearch.WordTrace]
  refine ⟨148249344683536299894694553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98832896455690866596463035 148249344683536299894694553)
  ·
    refine ⟨111187008512652224921020915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148249344683536299894694553 111187008512652224921020915)
    ·
      refine ⟨166780512768978337381531373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111187008512652224921020915 166780512768978337381531373)
      ·
        refine ⟨62542692288366876518074265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166780512768978337381531373 62542692288366876518074265)
        ·
          refine ⟨46907019216275157388555699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62542692288366876518074265 46907019216275157388555699)
          ·
            refine ⟨70360528824412736082833549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46907019216275157388555699 70360528824412736082833549)
            ·
              refine ⟨26385198309154776031062581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70360528824412736082833549 26385198309154776031062581)
              ·
                refine ⟨2473612341483260252912117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26385198309154776031062581 2473612341483260252912117)
                ·
                  refine ⟨231901157014055648710511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2473612341483260252912117 231901157014055648710511)
                  ·
                    rfl

theorem cell23_4064633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 5].length) (baseStart_4064633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064633 prefixEnd_4064633 := by exact prefixLift 4064633
  have htrace : WordTrace (prefixWord ++ tailWord_4064633) baseStart_4064633 baseEnd_4064633 := by
    simpa [prefixWord, tailWord_4064633, baseEnd_4064633] using wordTrace_append hprefix tailTrace_4064633
  have hstable : (prefixWord ++ tailWord_4064633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064633).length < 2 ^ (prefixWord ++ tailWord_4064633).sum := by decide
  have hdescent : baseEnd_4064633 < baseStart_4064633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064638 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4064638 : Nat := 118140960795 + 4064638 * 2 ^ 59
def prefixEnd_4064638 : Nat := 4983230072969 + 3 ^ 40 * 4064638 * 2
def baseEnd_4064638 : Nat := 2087112980529773318832077

theorem tailTrace_4064638 : CollatzResearch.WordTrace tailWord_4064638 prefixEnd_4064638 2087112980529773318832077 := by
  unfold tailWord_4064638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18531190881064773218578321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98833018032345457165751045 18531190881064773218578321)
  ·
    refine ⟨13898393160798579913933741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18531190881064773218578321 13898393160798579913933741)
    ·
      refine ⟨5211897435299467467725153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13898393160798579913933741 5211897435299467467725153)
      ·
        refine ⟨3908923076474600600793865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5211897435299467467725153 3908923076474600600793865)
        ·
          refine ⟨2931692307355950450595399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3908923076474600600793865 2931692307355950450595399)
          ·
            refine ⟨4397538461033925675893099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931692307355950450595399 4397538461033925675893099)
            ·
              refine ⟨6596307691550888513839649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397538461033925675893099 6596307691550888513839649)
              ·
                refine ⟨4947230768663166385379737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6596307691550888513839649 4947230768663166385379737)
                ·
                  refine ⟨3710423076497374789034803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4947230768663166385379737 3710423076497374789034803)
                  ·
                    refine ⟨5565634614746062183552205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3710423076497374789034803 5565634614746062183552205)
                    ·
                      refine ⟨2087112980529773318832077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5565634614746062183552205 2087112980529773318832077)
                      ·
                        rfl

theorem cell23_4064638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4064638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064638 prefixEnd_4064638 := by exact prefixLift 4064638
  have htrace : WordTrace (prefixWord ++ tailWord_4064638) baseStart_4064638 baseEnd_4064638 := by
    simpa [prefixWord, tailWord_4064638, baseEnd_4064638] using wordTrace_append hprefix tailTrace_4064638
  have hstable : (prefixWord ++ tailWord_4064638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064638).length < 2 ^ (prefixWord ++ tailWord_4064638).sum := by decide
  have hdescent : baseEnd_4064638 < baseStart_4064638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064643 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 3]
def baseStart_4064643 : Nat := 118140960795 + 4064643 * 2 ^ 59
def prefixEnd_4064643 : Nat := 4983230072969 + 3 ^ 40 * 4064643 * 2
def baseEnd_4064643 : Nat := 2087115547933045799269553

theorem tailTrace_4064643 : CollatzResearch.WordTrace tailWord_4064643 prefixEnd_4064643 2087115547933045799269553 := by
  unfold tailWord_4064643
  simp only [CollatzResearch.WordTrace]
  refine ⟨148249709413500071602558583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98833139609000047735039055 148249709413500071602558583)
  ·
    refine ⟨222374564120250107403837875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148249709413500071602558583 222374564120250107403837875)
    ·
      refine ⟨333561846180375161105756813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222374564120250107403837875 333561846180375161105756813)
      ·
        refine ⟨125085692317640685414658805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333561846180375161105756813 125085692317640685414658805)
        ·
          refine ⟨11726783654778814257624263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125085692317640685414658805 11726783654778814257624263)
          ·
            refine ⟨17590175482168221386436395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11726783654778814257624263 17590175482168221386436395)
            ·
              refine ⟨26385263223252332079654593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17590175482168221386436395 26385263223252332079654593)
              ·
                refine ⟨19788947417439249059740945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26385263223252332079654593 19788947417439249059740945)
                ·
                  refine ⟨14841710563079436794805709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19788947417439249059740945 14841710563079436794805709)
                  ·
                    refine ⟨5565641461154788798052141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14841710563079436794805709 5565641461154788798052141)
                    ·
                      refine ⟨2087115547933045799269553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5565641461154788798052141 2087115547933045799269553)
                      ·
                        rfl

theorem cell23_4064643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_4064643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064643 prefixEnd_4064643 := by exact prefixLift 4064643
  have htrace : WordTrace (prefixWord ++ tailWord_4064643) baseStart_4064643 baseEnd_4064643 := by
    simpa [prefixWord, tailWord_4064643, baseEnd_4064643] using wordTrace_append hprefix tailTrace_4064643
  have hstable : (prefixWord ++ tailWord_4064643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064643).length < 2 ^ (prefixWord ++ tailWord_4064643).sum := by decide
  have hdescent : baseEnd_4064643 < baseStart_4064643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064644 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_4064644 : Nat := 118140960795 + 4064644 * 2 ^ 59
def prefixEnd_4064644 : Nat := 4983230072969 + 3 ^ 40 * 4064644 * 2
def baseEnd_4064644 : Nat := 2087116061413700295357049

theorem tailTrace_4064644 : CollatzResearch.WordTrace tailWord_4064644 prefixEnd_4064644 2087116061413700295357049 := by
  unfold tailWord_4064644
  simp only [CollatzResearch.WordTrace]
  refine ⟨74124872943248224386672493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98833163924330965848896657 74124872943248224386672493)
  ·
    refine ⟨27796827353718084145002185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74124872943248224386672493 27796827353718084145002185)
    ·
      refine ⟨20847620515288563108751639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27796827353718084145002185 20847620515288563108751639)
      ·
        refine ⟨31271430772932844663127459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20847620515288563108751639 31271430772932844663127459)
        ·
          refine ⟨46907146159399266994691189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31271430772932844663127459 46907146159399266994691189)
          ·
            refine ⟨4397544952443681280752299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46907146159399266994691189 4397544952443681280752299)
            ·
              refine ⟨6596317428665521921128449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397544952443681280752299 6596317428665521921128449)
              ·
                refine ⟨4947238071499141440846337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6596317428665521921128449 4947238071499141440846337)
                ·
                  refine ⟨3710428553624356080634753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4947238071499141440846337 3710428553624356080634753)
                  ·
                    refine ⟨2782821415218267060476065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3710428553624356080634753 2782821415218267060476065)
                    ·
                      refine ⟨2087116061413700295357049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782821415218267060476065 2087116061413700295357049)
                      ·
                        rfl

theorem cell23_4064644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_4064644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064644 prefixEnd_4064644 := by exact prefixLift 4064644
  have htrace : WordTrace (prefixWord ++ tailWord_4064644) baseStart_4064644 baseEnd_4064644 := by
    simpa [prefixWord, tailWord_4064644, baseEnd_4064644] using wordTrace_append hprefix tailTrace_4064644
  have hstable : (prefixWord ++ tailWord_4064644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064644).length < 2 ^ (prefixWord ++ tailWord_4064644).sum := by decide
  have hdescent : baseEnd_4064644 < baseStart_4064644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064660 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_4064660 : Nat := 118140960795 + 4064660 * 2 ^ 59
def prefixEnd_4064660 : Nat := 4983230072969 + 3 ^ 40 * 4064660 * 2
def baseEnd_4064660 : Nat := 2087124277104172232756975

theorem tailTrace_4064660 : CollatzResearch.WordTrace tailWord_4064660 prefixEnd_4064660 2087124277104172232756975 := by
  unfold tailWord_4064660
  simp only [CollatzResearch.WordTrace]
  refine ⟨74125164727219241752963717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98833552969625655670618289 74125164727219241752963717)
  ·
    refine ⟨13898468386353607828680697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74125164727219241752963717 13898468386353607828680697)
    ·
      refine ⟨10423851289765205871510523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13898468386353607828680697 10423851289765205871510523)
      ·
        refine ⟨15635776934647808807265785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10423851289765205871510523 15635776934647808807265785)
        ·
          refine ⟨11726832700985856605449339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15635776934647808807265785 11726832700985856605449339)
          ·
            refine ⟨17590249051478784908174009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11726832700985856605449339 17590249051478784908174009)
            ·
              refine ⟨13192686788609088681130507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17590249051478784908174009 13192686788609088681130507)
              ·
                refine ⟨19789030182913633021695761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13192686788609088681130507 19789030182913633021695761)
                ·
                  refine ⟨14841772637185224766271821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19789030182913633021695761 14841772637185224766271821)
                  ·
                    refine ⟨5565664738944459287351933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14841772637185224766271821 5565664738944459287351933)
                    ·
                      refine ⟨2087124277104172232756975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5565664738944459287351933 2087124277104172232756975)
                      ·
                        rfl

theorem cell23_4064660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_4064660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064660 prefixEnd_4064660 := by exact prefixLift 4064660
  have htrace : WordTrace (prefixWord ++ tailWord_4064660) baseStart_4064660 baseEnd_4064660 := by
    simpa [prefixWord, tailWord_4064660, baseEnd_4064660] using wordTrace_append hprefix tailTrace_4064660
  have hstable : (prefixWord ++ tailWord_4064660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064660).length < 2 ^ (prefixWord ++ tailWord_4064660).sum := by decide
  have hdescent : baseEnd_4064660 < baseStart_4064660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064676 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_4064676 : Nat := 118140960795 + 4064676 * 2 ^ 59
def prefixEnd_4064676 : Nat := 4983230072969 + 3 ^ 40 * 4064676 * 2
def baseEnd_4064676 : Nat := 695710830931548056718967

theorem tailTrace_4064676 : CollatzResearch.WordTrace tailWord_4064676 prefixEnd_4064676 695710830931548056718967 := by
  unfold tailWord_4064676
  simp only [CollatzResearch.WordTrace]
  refine ⟨74125456511190259119254941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98833942014920345492339921 74125456511190259119254941)
  ·
    refine ⟨27797046191696347169720603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74125456511190259119254941 27797046191696347169720603)
    ·
      refine ⟨41695569287544520754580905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27797046191696347169720603 41695569287544520754580905)
      ·
        refine ⟨31271676965658390565935679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41695569287544520754580905 31271676965658390565935679)
        ·
          refine ⟨46907515448487585848903519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31271676965658390565935679 46907515448487585848903519)
          ·
            refine ⟨70361273172731378773355279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46907515448487585848903519 70361273172731378773355279)
            ·
              refine ⟨105541909759097068160032919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70361273172731378773355279 105541909759097068160032919)
              ·
                refine ⟨158312864638645602240049379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105541909759097068160032919 158312864638645602240049379)
                ·
                  refine ⟨237469296957968403360074069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158312864638645602240049379 237469296957968403360074069)
                  ·
                    refine ⟨695710830931548056718967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 237469296957968403360074069 695710830931548056718967)
                    ·
                      rfl

theorem cell23_4064676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_4064676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064676 prefixEnd_4064676 := by exact prefixLift 4064676
  have htrace : WordTrace (prefixWord ++ tailWord_4064676) baseStart_4064676 baseEnd_4064676 := by
    simpa [prefixWord, tailWord_4064676, baseEnd_4064676] using wordTrace_append hprefix tailTrace_4064676
  have hstable : (prefixWord ++ tailWord_4064676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064676).length < 2 ^ (prefixWord ++ tailWord_4064676).sum := by decide
  have hdescent : baseEnd_4064676 < baseStart_4064676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064696 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_4064696 : Nat := 118140960795 + 4064696 * 2 ^ 59
def prefixEnd_4064696 : Nat := 4983230072969 + 3 ^ 40 * 4064696 * 2
def baseEnd_4064696 : Nat := 2087142762407734091906809

theorem tailTrace_4064696 : CollatzResearch.WordTrace tailWord_4064696 prefixEnd_4064696 2087142762407734091906809 := by
  unfold tailWord_4064696
  simp only [CollatzResearch.WordTrace]
  refine ⟨74125821241154030827118971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98834428321538707769491961 74125821241154030827118971)
  ·
    refine ⟨111188731861731046240678457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74125821241154030827118971 111188731861731046240678457)
    ·
      refine ⟨83391548896298284680508843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111188731861731046240678457 83391548896298284680508843)
      ·
        refine ⟨125087323344447427020763265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83391548896298284680508843 125087323344447427020763265)
        ·
          refine ⟨93815492508335570265572449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125087323344447427020763265 93815492508335570265572449)
          ·
            refine ⟨70361619381251677699179337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93815492508335570265572449 70361619381251677699179337)
            ·
              refine ⟨52771214535938758274384503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70361619381251677699179337 52771214535938758274384503)
              ·
                refine ⟨79156821803908137411576755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52771214535938758274384503 79156821803908137411576755)
                ·
                  refine ⟨118735232705862206117365133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79156821803908137411576755 118735232705862206117365133)
                  ·
                    refine ⟨44525712264698327294011925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118735232705862206117365133 44525712264698327294011925)
                    ·
                      refine ⟨2087142762407734091906809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44525712264698327294011925 2087142762407734091906809)
                      ·
                        rfl

theorem cell23_4064696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_4064696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064696 prefixEnd_4064696 := by exact prefixLift 4064696
  have htrace : WordTrace (prefixWord ++ tailWord_4064696) baseStart_4064696 baseEnd_4064696 := by
    simpa [prefixWord, tailWord_4064696, baseEnd_4064696] using wordTrace_append hprefix tailTrace_4064696
  have hstable : (prefixWord ++ tailWord_4064696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064696).length < 2 ^ (prefixWord ++ tailWord_4064696).sum := by decide
  have hdescent : baseEnd_4064696 < baseStart_4064696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064757 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 6]
def baseStart_4064757 : Nat := 118140960795 + 4064757 * 2 ^ 59
def prefixEnd_4064757 : Nat := 4983230072969 + 3 ^ 40 * 4064757 * 2
def baseEnd_4064757 : Nat := 231908231636406483693781

theorem tailTrace_4064757 : CollatzResearch.WordTrace tailWord_4064757 prefixEnd_4064757 231908231636406483693781 := by
  unfold tailWord_4064757
  simp only [CollatzResearch.WordTrace]
  refine ⟨148253867335087069072208525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98835911556724712714805683 148253867335087069072208525)
  ·
    refine ⟨55595200250657650902078197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148253867335087069072208525 55595200250657650902078197)
    ·
      refine ⟨5212050023499154772069831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55595200250657650902078197 5212050023499154772069831)
      ·
        refine ⟨7818075035248732158104747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212050023499154772069831 7818075035248732158104747)
        ·
          refine ⟨11727112552873098237157121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7818075035248732158104747 11727112552873098237157121)
          ·
            refine ⟨8795334414654823677867841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11727112552873098237157121 8795334414654823677867841)
            ·
              refine ⟨6596500810991117758400881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8795334414654823677867841 6596500810991117758400881)
              ·
                refine ⟨4947375608243338318800661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6596500810991117758400881 4947375608243338318800661)
                ·
                  refine ⟨231908231636406483693781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4947375608243338318800661 231908231636406483693781)
                  ·
                    rfl

theorem cell23_4064757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_4064757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064757 prefixEnd_4064757 := by exact prefixLift 4064757
  have htrace : WordTrace (prefixWord ++ tailWord_4064757) baseStart_4064757 baseEnd_4064757 := by
    simpa [prefixWord, tailWord_4064757, baseEnd_4064757] using wordTrace_append hprefix tailTrace_4064757
  have hstable : (prefixWord ++ tailWord_4064757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064757).length < 2 ^ (prefixWord ++ tailWord_4064757).sum := by decide
  have hdescent : baseEnd_4064757 < baseStart_4064757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064800 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 1, 6]
def baseStart_4064800 : Nat := 118140960795 + 4064800 * 2 ^ 59
def prefixEnd_4064800 : Nat := 4983230072969 + 3 ^ 40 * 4064800 * 2
def baseEnd_4064800 : Nat := 695732054798600561668777

theorem tailTrace_4064800 : CollatzResearch.WordTrace tailWord_4064800 prefixEnd_4064800 695732054798600561668777 := by
  unfold tailWord_4064800
  simp only [CollatzResearch.WordTrace]
  refine ⟨74127717836965643708011927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98836957115954191610682569 74127717836965643708011927)
  ·
    refine ⟨111191576755448465562017891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74127717836965643708011927 111191576755448465562017891)
    ·
      refine ⟨166787365133172698343026837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111191576755448465562017891 166787365133172698343026837)
      ·
        refine ⟨7818157740617470234829383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166787365133172698343026837 7818157740617470234829383)
        ·
          refine ⟨11727236610926205352244075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7818157740617470234829383 11727236610926205352244075)
          ·
            refine ⟨17590854916389308028366113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11727236610926205352244075 17590854916389308028366113)
            ·
              refine ⟨13193141187291981021274585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17590854916389308028366113 13193141187291981021274585)
              ·
                refine ⟨9894855890468985765955939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13193141187291981021274585 9894855890468985765955939)
                ·
                  refine ⟨14842283835703478648933909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9894855890468985765955939 14842283835703478648933909)
                  ·
                    refine ⟨695732054798600561668777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14842283835703478648933909 695732054798600561668777)
                    ·
                      rfl

theorem cell23_4064800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_4064800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064800 prefixEnd_4064800 := by exact prefixLift 4064800
  have htrace : WordTrace (prefixWord ++ tailWord_4064800) baseStart_4064800 baseEnd_4064800 := by
    simpa [prefixWord, tailWord_4064800, baseEnd_4064800] using wordTrace_append hprefix tailTrace_4064800
  have hstable : (prefixWord ++ tailWord_4064800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064800).length < 2 ^ (prefixWord ++ tailWord_4064800).sum := by decide
  have hdescent : baseEnd_4064800 < baseStart_4064800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064810 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_4064810 : Nat := 118140960795 + 4064810 * 2 ^ 59
def prefixEnd_4064810 : Nat := 4983230072969 + 3 ^ 40 * 4064810 * 2
def baseEnd_4064810 : Nat := 2087201299202346645881285

theorem tailTrace_4064810 : CollatzResearch.WordTrace tailWord_4064810 prefixEnd_4064810 2087201299202346645881285 := by
  unfold tailWord_4064810
  simp only [CollatzResearch.WordTrace]
  refine ⟨37063950100973764780971971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98837200269263372749258589 37063950100973764780971971)
  ·
    refine ⟨55595925151460647171457957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37063950100973764780971971 55595925151460647171457957)
    ·
      refine ⟨10424235965898871344648367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55595925151460647171457957 10424235965898871344648367)
      ·
        refine ⟨15636353948848307016972551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10424235965898871344648367 15636353948848307016972551)
        ·
          refine ⟨23454530923272460525458827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15636353948848307016972551 23454530923272460525458827)
          ·
            refine ⟨35181796384908690788188241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23454530923272460525458827 35181796384908690788188241)
            ·
              refine ⟨26386347288681518091141181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35181796384908690788188241 26386347288681518091141181)
              ·
                refine ⟨9894880233255569284177943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26386347288681518091141181 9894880233255569284177943)
                ·
                  refine ⟨14842320349883353926266915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9894880233255569284177943 14842320349883353926266915)
                  ·
                    refine ⟨22263480524825030889400373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14842320349883353926266915 22263480524825030889400373)
                    ·
                      refine ⟨2087201299202346645881285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22263480524825030889400373 2087201299202346645881285)
                      ·
                        rfl

theorem cell23_4064810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_4064810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064810 prefixEnd_4064810 := by exact prefixLift 4064810
  have htrace : WordTrace (prefixWord ++ tailWord_4064810) baseStart_4064810 baseEnd_4064810 := by
    simpa [prefixWord, tailWord_4064810, baseEnd_4064810] using wordTrace_append hprefix tailTrace_4064810
  have hstable : (prefixWord ++ tailWord_4064810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064810).length < 2 ^ (prefixWord ++ tailWord_4064810).sum := by decide
  have hdescent : baseEnd_4064810 < baseStart_4064810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064824 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 3, 2, 2]
def baseStart_4064824 : Nat := 118140960795 + 4064824 * 2 ^ 59
def prefixEnd_4064824 : Nat := 4983230072969 + 3 ^ 40 * 4064824 * 2
def baseEnd_4064824 : Nat := 2087208487931509591106221

theorem tailTrace_4064824 : CollatzResearch.WordTrace tailWord_4064824 prefixEnd_4064824 2087208487931509591106221 := by
  unfold tailWord_4064824
  simp only [CollatzResearch.WordTrace]
  refine ⟨74128155512922169757448763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98837540683896226343265017 74128155512922169757448763)
  ·
    refine ⟨111192233269383254636173145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74128155512922169757448763 111192233269383254636173145)
    ·
      refine ⟨83394174952037440977129859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111192233269383254636173145 83394174952037440977129859)
      ·
        refine ⟨125091262428056161465694789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83394174952037440977129859 125091262428056161465694789)
        ·
          refine ⟨23454611705260530274817773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125091262428056161465694789 23454611705260530274817773)
          ·
            refine ⟨8795479389472698853056665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23454611705260530274817773 8795479389472698853056665)
            ·
              refine ⟨6596609542104524139792499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8795479389472698853056665 6596609542104524139792499)
              ·
                refine ⟨9894914313156786209688749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596609542104524139792499 9894914313156786209688749)
                ·
                  refine ⟨3710592867433794828633281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9894914313156786209688749 3710592867433794828633281)
                  ·
                    refine ⟨2782944650575346121474961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3710592867433794828633281 2782944650575346121474961)
                    ·
                      refine ⟨2087208487931509591106221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2782944650575346121474961 2087208487931509591106221)
                      ·
                        rfl

theorem cell23_4064824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_4064824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064824 prefixEnd_4064824 := by exact prefixLift 4064824
  have htrace : WordTrace (prefixWord ++ tailWord_4064824) baseStart_4064824 baseEnd_4064824 := by
    simpa [prefixWord, tailWord_4064824, baseEnd_4064824] using wordTrace_append hprefix tailTrace_4064824
  have hstable : (prefixWord ++ tailWord_4064824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064824).length < 2 ^ (prefixWord ++ tailWord_4064824).sum := by decide
  have hdescent : baseEnd_4064824 < baseStart_4064824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064863 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_4064863 : Nat := 118140960795 + 4064863 * 2 ^ 59
def prefixEnd_4064863 : Nat := 4983230072969 + 3 ^ 40 * 4064863 * 2
def baseEnd_4064863 : Nat := 2087228513677034938518541

theorem tailTrace_4064863 : CollatzResearch.WordTrace tailWord_4064863 prefixEnd_4064863 2087228513677034938518541 := by
  unfold tailWord_4064863
  simp only [CollatzResearch.WordTrace]
  refine ⟨148257733472703049175567243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98838488981802032783711495 148257733472703049175567243)
  ·
    refine ⟨222386600209054573763350865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148257733472703049175567243 222386600209054573763350865)
    ·
      refine ⟨166789950156790930322513149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222386600209054573763350865 166789950156790930322513149)
      ·
        refine ⟨62546231308796598870942431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166789950156790930322513149 62546231308796598870942431)
        ·
          refine ⟨93819346963194898306413647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62546231308796598870942431 93819346963194898306413647)
          ·
            refine ⟨140729020444792347459620471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93819346963194898306413647 140729020444792347459620471)
            ·
              refine ⟨211093530667188521189430707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140729020444792347459620471 211093530667188521189430707)
              ·
                refine ⟨316640296000782781784146061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211093530667188521189430707 316640296000782781784146061)
                ·
                  refine ⟨118740111000293543169054773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316640296000782781784146061 118740111000293543169054773)
                  ·
                    refine ⟨11131885406277519672098885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118740111000293543169054773 11131885406277519672098885)
                    ·
                      refine ⟨2087228513677034938518541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11131885406277519672098885 2087228513677034938518541)
                      ·
                        rfl

theorem cell23_4064863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_4064863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064863 prefixEnd_4064863 := by exact prefixLift 4064863
  have htrace : WordTrace (prefixWord ++ tailWord_4064863) baseStart_4064863 baseEnd_4064863 := by
    simpa [prefixWord, tailWord_4064863, baseEnd_4064863] using wordTrace_append hprefix tailTrace_4064863
  have hstable : (prefixWord ++ tailWord_4064863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064863).length < 2 ^ (prefixWord ++ tailWord_4064863).sum := by decide
  have hdescent : baseEnd_4064863 < baseStart_4064863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064873 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 4, 6]
def baseStart_4064873 : Nat := 118140960795 + 4064873 * 2 ^ 59
def prefixEnd_4064873 : Nat := 4983230072969 + 3 ^ 40 * 4064873 * 2
def baseEnd_4064873 : Nat := 695744549494526633131165

theorem tailTrace_4064873 : CollatzResearch.WordTrace tailWord_4064873 prefixEnd_4064873 695744549494526633131165 := by
  unfold tailWord_4064873
  simp only [CollatzResearch.WordTrace]
  refine ⟨148258098202666820883431273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98838732135111213922287515 148258098202666820883431273)
  ·
    refine ⟨111193573652000115662573455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148258098202666820883431273 111193573652000115662573455)
    ·
      refine ⟨166790360478000173493860183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111193573652000115662573455 166790360478000173493860183)
      ·
        refine ⟨250185540717000260240790275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166790360478000173493860183 250185540717000260240790275)
        ·
          refine ⟨375278311075500390361185413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250185540717000260240790275 375278311075500390361185413)
          ·
            refine ⟨70364683326656323192722265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375278311075500390361185413 70364683326656323192722265)
            ·
              refine ⟨52773512494992242394541699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70364683326656323192722265 52773512494992242394541699)
              ·
                refine ⟨79160268742488363591812549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52773512494992242394541699 79160268742488363591812549)
                ·
                  refine ⟨14842550389216568173464853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79160268742488363591812549 14842550389216568173464853)
                  ·
                    refine ⟨695744549494526633131165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14842550389216568173464853 695744549494526633131165)
                    ·
                      rfl

theorem cell23_4064873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_4064873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064873 prefixEnd_4064873 := by exact prefixLift 4064873
  have htrace : WordTrace (prefixWord ++ tailWord_4064873) baseStart_4064873 baseEnd_4064873 := by
    simpa [prefixWord, tailWord_4064873, baseEnd_4064873] using wordTrace_append hprefix tailTrace_4064873
  have hstable : (prefixWord ++ tailWord_4064873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064873).length < 2 ^ (prefixWord ++ tailWord_4064873).sum := by decide
  have hdescent : baseEnd_4064873 < baseStart_4064873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064913 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_4064913 : Nat := 118140960795 + 4064913 * 2 ^ 59
def prefixEnd_4064913 : Nat := 4983230072969 + 3 ^ 40 * 4064913 * 2
def baseEnd_4064913 : Nat := 2087254187709759742893311

theorem tailTrace_4064913 : CollatzResearch.WordTrace tailWord_4064913 prefixEnd_4064913 2087254187709759742893311 := by
  unfold tailWord_4064913
  simp only [CollatzResearch.WordTrace]
  refine ⟨148259557122521907714887393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98839704748347938476591595 148259557122521907714887393)
  ·
    refine ⟨111194667841891430786165545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148259557122521907714887393 111194667841891430786165545)
    ·
      refine ⟨83396000881418573089624159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111194667841891430786165545 83396000881418573089624159)
      ·
        refine ⟨125094001322127859634436239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83396000881418573089624159 125094001322127859634436239)
        ·
          refine ⟨187641001983191789451654359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125094001322127859634436239 187641001983191789451654359)
          ·
            refine ⟨281461502974787684177481539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187641001983191789451654359 281461502974787684177481539)
            ·
              refine ⟨422192254462181526266222309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281461502974787684177481539 422192254462181526266222309)
              ·
                refine ⟨79161047711659036174916683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422192254462181526266222309 79161047711659036174916683)
                ·
                  refine ⟨118741571567488554262375025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79161047711659036174916683 118741571567488554262375025)
                  ·
                    refine ⟨89056178675616415696781269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118741571567488554262375025 89056178675616415696781269)
                    ·
                      refine ⟨2087254187709759742893311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89056178675616415696781269 2087254187709759742893311)
                      ·
                        rfl

theorem cell23_4064913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_4064913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064913 prefixEnd_4064913 := by exact prefixLift 4064913
  have htrace : WordTrace (prefixWord ++ tailWord_4064913) baseStart_4064913 baseEnd_4064913 := by
    simpa [prefixWord, tailWord_4064913, baseEnd_4064913] using wordTrace_append hprefix tailTrace_4064913
  have hstable : (prefixWord ++ tailWord_4064913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064913).length < 2 ^ (prefixWord ++ tailWord_4064913).sum := by decide
  have hdescent : baseEnd_4064913 < baseStart_4064913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064957 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_4064957 : Nat := 118140960795 + 4064957 * 2 ^ 59
def prefixEnd_4064957 : Nat := 4983230072969 + 3 ^ 40 * 4064957 * 2
def baseEnd_4064957 : Nat := 2087276780858557570743109

theorem tailTrace_4064957 : CollatzResearch.WordTrace tailWord_4064957 prefixEnd_4064957 2087276780858557570743109 := by
  unfold tailWord_4064957
  simp only [CollatzResearch.WordTrace]
  refine ⟨148261161934362503229489125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98840774622908335486326083 148261161934362503229489125)
  ·
    refine ⟨27798967862692969355529211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148261161934362503229489125 27798967862692969355529211)
    ·
      refine ⟨41698451794039454033293817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27798967862692969355529211 41698451794039454033293817)
      ·
        refine ⟨31273838845529590524970363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41698451794039454033293817 31273838845529590524970363)
        ·
          refine ⟨46910758268294385787455545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31273838845529590524970363 46910758268294385787455545)
          ·
            refine ⟨35183068701220789340591659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46910758268294385787455545 35183068701220789340591659)
            ·
              refine ⟨52774603051831184010887489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35183068701220789340591659 52774603051831184010887489)
              ·
                refine ⟨39580952288873388008165617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52774603051831184010887489 39580952288873388008165617)
                ·
                  refine ⟨29685714216655041006124213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39580952288873388008165617 29685714216655041006124213)
                  ·
                    refine ⟨2783035707811410094324145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29685714216655041006124213 2783035707811410094324145)
                    ·
                      refine ⟨2087276780858557570743109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783035707811410094324145 2087276780858557570743109)
                      ·
                        rfl

theorem cell23_4064957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_4064957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064957 prefixEnd_4064957 := by exact prefixLift 4064957
  have htrace : WordTrace (prefixWord ++ tailWord_4064957) baseStart_4064957 baseEnd_4064957 := by
    simpa [prefixWord, tailWord_4064957, baseEnd_4064957] using wordTrace_append hprefix tailTrace_4064957
  have hstable : (prefixWord ++ tailWord_4064957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064957).length < 2 ^ (prefixWord ++ tailWord_4064957).sum := by decide
  have hdescent : baseEnd_4064957 < baseStart_4064957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064982 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4064982 : Nat := 118140960795 + 4064982 * 2 ^ 59
def prefixEnd_4064982 : Nat := 4983230072969 + 3 ^ 40 * 4064982 * 2
def baseEnd_4064982 : Nat := 2087289617874919972930495

theorem tailTrace_4064982 : CollatzResearch.WordTrace tailWord_4064982 prefixEnd_4064982 2087289617874919972930495 := by
  unfold tailWord_4064982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9266379609954495781196825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98841382506181288332766133 9266379609954495781196825)
  ·
    refine ⟨6949784707465871835897619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9266379609954495781196825 6949784707465871835897619)
    ·
      refine ⟨10424677061198807753846429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6949784707465871835897619 10424677061198807753846429)
      ·
        refine ⟨3909253897949552907692411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10424677061198807753846429 3909253897949552907692411)
        ·
          refine ⟨5863880846924329361538617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909253897949552907692411 5863880846924329361538617)
          ·
            refine ⟨4397910635193247021153963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5863880846924329361538617 4397910635193247021153963)
            ·
              refine ⟨6596865952789870531730945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397910635193247021153963 6596865952789870531730945)
              ·
                refine ⟨4947649464592402898798209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6596865952789870531730945 4947649464592402898798209)
                ·
                  refine ⟨3710737098444302174098657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4947649464592402898798209 3710737098444302174098657)
                  ·
                    refine ⟨2783052823833226630573993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3710737098444302174098657 2783052823833226630573993)
                    ·
                      refine ⟨2087289617874919972930495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783052823833226630573993 2087289617874919972930495)
                      ·
                        rfl

theorem cell23_4064982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4064982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4064982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4064982 prefixEnd_4064982 := by exact prefixLift 4064982
  have htrace : WordTrace (prefixWord ++ tailWord_4064982) baseStart_4064982 baseEnd_4064982 := by
    simpa [prefixWord, tailWord_4064982, baseEnd_4064982] using wordTrace_append hprefix tailTrace_4064982
  have hstable : (prefixWord ++ tailWord_4064982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064982).length < 2 ^ (prefixWord ++ tailWord_4064982).sum := by decide
  have hdescent : baseEnd_4064982 < baseStart_4064982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065014 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_4065014 : Nat := 118140960795 + 4065014 * 2 ^ 59
def prefixEnd_4065014 : Nat := 4983230072969 + 3 ^ 40 * 4065014 * 2
def baseEnd_4065014 : Nat := 695768683085287949243449

theorem tailTrace_4065014 : CollatzResearch.WordTrace tailWord_4065014 prefixEnd_4065014 695768683085287949243449 := by
  unfold tailWord_4065014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9266452555947250122769631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98842160596770667976209397 9266452555947250122769631)
  ·
    refine ⟨13899678833920875184154447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9266452555947250122769631 13899678833920875184154447)
    ·
      refine ⟨20849518250881312776231671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13899678833920875184154447 20849518250881312776231671)
      ·
        refine ⟨31274277376321969164347507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20849518250881312776231671 31274277376321969164347507)
        ·
          refine ⟨46911416064482953746521261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31274277376321969164347507 46911416064482953746521261)
          ·
            refine ⟨17591781024181107654945473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46911416064482953746521261 17591781024181107654945473)
            ·
              refine ⟨13193835768135830741209105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17591781024181107654945473 13193835768135830741209105)
              ·
                refine ⟨9895376826101873055906829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13193835768135830741209105 9895376826101873055906829)
                ·
                  refine ⟨3710766309788202395965061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9895376826101873055906829 3710766309788202395965061)
                  ·
                    refine ⟨695768683085287949243449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3710766309788202395965061 695768683085287949243449)
                    ·
                      rfl

theorem cell23_4065014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_4065014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065014 prefixEnd_4065014 := by exact prefixLift 4065014
  have htrace : WordTrace (prefixWord ++ tailWord_4065014) baseStart_4065014 baseEnd_4065014 := by
    simpa [prefixWord, tailWord_4065014, baseEnd_4065014] using wordTrace_append hprefix tailTrace_4065014
  have hstable : (prefixWord ++ tailWord_4065014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065014).length < 2 ^ (prefixWord ++ tailWord_4065014).sum := by decide
  have hdescent : baseEnd_4065014 < baseStart_4065014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065074 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_4065074 : Nat := 118140960795 + 4065074 * 2 ^ 59
def prefixEnd_4065074 : Nat := 4983230072969 + 3 ^ 40 * 4065074 * 2
def baseEnd_4065074 : Nat := 695778952698377870993357

theorem tailTrace_4065074 : CollatzResearch.WordTrace tailWord_4065074 prefixEnd_4065074 695778952698377870993357 := by
  unfold tailWord_4065074
  simp only [CollatzResearch.WordTrace]
  refine ⟨37066357318734658052874569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98843619516625754807665517 37066357318734658052874569)
  ·
    refine ⟨27799767989050993539655927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37066357318734658052874569 27799767989050993539655927)
    ·
      refine ⟨41699651983576490309483891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27799767989050993539655927 41699651983576490309483891)
      ·
        refine ⟨62549477975364735464225837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41699651983576490309483891 62549477975364735464225837)
        ·
          refine ⟨23456054240761775799084689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62549477975364735464225837 23456054240761775799084689)
          ·
            refine ⟨17592040680571331849313517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23456054240761775799084689 17592040680571331849313517)
            ·
              refine ⟨6597015255214249443492569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17592040680571331849313517 6597015255214249443492569)
              ·
                refine ⟨4947761441410687082619427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6597015255214249443492569 4947761441410687082619427)
                ·
                  refine ⟨7421642162116030623929141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947761441410687082619427 7421642162116030623929141)
                  ·
                    refine ⟨695778952698377870993357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7421642162116030623929141 695778952698377870993357)
                    ·
                      rfl

theorem cell23_4065074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_4065074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065074 prefixEnd_4065074 := by exact prefixLift 4065074
  have htrace : WordTrace (prefixWord ++ tailWord_4065074) baseStart_4065074 baseEnd_4065074 := by
    simpa [prefixWord, tailWord_4065074, baseEnd_4065074] using wordTrace_append hprefix tailTrace_4065074
  have hstable : (prefixWord ++ tailWord_4065074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065074).length < 2 ^ (prefixWord ++ tailWord_4065074).sum := by decide
  have hdescent : baseEnd_4065074 < baseStart_4065074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065100 : List Nat := [2, 2, 1, 3, 15]
def baseStart_4065100 : Nat := 118140960795 + 4065100 * 2 ^ 59
def prefixEnd_4065100 : Nat := 4983230072969 + 3 ^ 40 * 4065100 * 2
def baseEnd_4065100 : Nat := 2863306184625720865919

theorem tailTrace_4065100 : CollatzResearch.WordTrace tailWord_4065100 prefixEnd_4065100 2863306184625720865919 := by
  unfold tailWord_4065100
  simp only [CollatzResearch.WordTrace]
  refine ⟨74133188786422219325972377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98844251715229625767963169 74133188786422219325972377)
  ·
    refine ⟨55599891589816664494479283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74133188786422219325972377 55599891589816664494479283)
    ·
      refine ⟨83399837384724996741718925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55599891589816664494479283 83399837384724996741718925)
      ·
        refine ⟨31274939019271873778144597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83399837384724996741718925 31274939019271873778144597)
        ·
          refine ⟨2863306184625720865919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 31274939019271873778144597 2863306184625720865919)
          ·
            rfl

theorem cell23_4065100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 15].length) (baseStart_4065100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065100 prefixEnd_4065100 := by exact prefixLift 4065100
  have htrace : WordTrace (prefixWord ++ tailWord_4065100) baseStart_4065100 baseEnd_4065100 := by
    simpa [prefixWord, tailWord_4065100, baseEnd_4065100] using wordTrace_append hprefix tailTrace_4065100
  have hstable : (prefixWord ++ tailWord_4065100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065100).length < 2 ^ (prefixWord ++ tailWord_4065100).sum := by decide
  have hdescent : baseEnd_4065100 < baseStart_4065100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065105 : List Nat := [1, 2, 2, 1, 5, 3, 2, 2, 1, 1, 3]
def baseStart_4065105 : Nat := 118140960795 + 4065105 * 2 ^ 59
def prefixEnd_4065105 : Nat := 4983230072969 + 3 ^ 40 * 4065105 * 2
def baseEnd_4065105 : Nat := 2087352775995422991692429

theorem tailTrace_4065105 : CollatzResearch.WordTrace tailWord_4065105 prefixEnd_4065105 2087352775995422991692429 := by
  unfold tailWord_4065105
  simp only [CollatzResearch.WordTrace]
  refine ⟨148266559937826324505876769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98844373291884216337251179 148266559937826324505876769)
  ·
    refine ⟨111199919953369743379407577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148266559937826324505876769 111199919953369743379407577)
    ·
      refine ⟨83399939965027307534555683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111199919953369743379407577 83399939965027307534555683)
      ·
        refine ⟨125099909947540961301833525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83399939965027307534555683 125099909947540961301833525)
        ·
          refine ⟨11728116557581965122046893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125099909947540961301833525 11728116557581965122046893)
          ·
            refine ⟨4398043709093236920767585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11728116557581965122046893 4398043709093236920767585)
            ·
              refine ⟨3298532781819927690575689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4398043709093236920767585 3298532781819927690575689)
              ·
                refine ⟨2473899586364945767931767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298532781819927690575689 2473899586364945767931767)
                ·
                  refine ⟨3710849379547418651897651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473899586364945767931767 3710849379547418651897651)
                  ·
                    refine ⟨5566274069321127977846477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3710849379547418651897651 5566274069321127977846477)
                    ·
                      refine ⟨2087352775995422991692429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5566274069321127977846477 2087352775995422991692429)
                      ·
                        rfl

theorem cell23_4065105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 1, 3].length) (baseStart_4065105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065105 prefixEnd_4065105 := by exact prefixLift 4065105
  have htrace : WordTrace (prefixWord ++ tailWord_4065105) baseStart_4065105 baseEnd_4065105 := by
    simpa [prefixWord, tailWord_4065105, baseEnd_4065105] using wordTrace_append hprefix tailTrace_4065105
  have hstable : (prefixWord ++ tailWord_4065105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065105).length < 2 ^ (prefixWord ++ tailWord_4065105).sum := by decide
  have hdescent : baseEnd_4065105 < baseStart_4065105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065177 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 2, 6]
def baseStart_4065177 : Nat := 118140960795 + 4065177 * 2 ^ 59
def prefixEnd_4065177 : Nat := 4983230072969 + 3 ^ 40 * 4065177 * 2
def baseEnd_4065177 : Nat := 695796582200848903330699

theorem tailTrace_4065177 : CollatzResearch.WordTrace tailWord_4065177 prefixEnd_4065177 695796582200848903330699 := by
  unfold tailWord_4065177
  simp only [CollatzResearch.WordTrace]
  refine ⟨148269185993565480802497785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98846123995710320534998523 148269185993565480802497785)
  ·
    refine ⟨111201889495174110601873339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148269185993565480802497785 111201889495174110601873339)
    ·
      refine ⟨166802834242761165902810009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111201889495174110601873339 166802834242761165902810009)
      ·
        refine ⟨125102125682070874427107507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166802834242761165902810009 125102125682070874427107507)
        ·
          refine ⟨187653188523106311640661261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125102125682070874427107507 187653188523106311640661261)
          ·
            refine ⟨70369945696164866865247973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187653188523106311640661261 70369945696164866865247973)
            ·
              refine ⟨13194364818030912537233995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70369945696164866865247973 13194364818030912537233995)
              ·
                refine ⟨19791547227046368805850993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13194364818030912537233995 19791547227046368805850993)
                ·
                  refine ⟨14843660420284776604388245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19791547227046368805850993 14843660420284776604388245)
                  ·
                    refine ⟨695796582200848903330699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14843660420284776604388245 695796582200848903330699)
                    ·
                      rfl

theorem cell23_4065177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_4065177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065177 prefixEnd_4065177 := by exact prefixLift 4065177
  have htrace : WordTrace (prefixWord ++ tailWord_4065177) baseStart_4065177 baseEnd_4065177 := by
    simpa [prefixWord, tailWord_4065177, baseEnd_4065177] using wordTrace_append hprefix tailTrace_4065177
  have hstable : (prefixWord ++ tailWord_4065177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065177).length < 2 ^ (prefixWord ++ tailWord_4065177).sum := by decide
  have hdescent : baseEnd_4065177 < baseStart_4065177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065187 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 5]
def baseStart_4065187 : Nat := 118140960795 + 4065187 * 2 ^ 59
def prefixEnd_4065187 : Nat := 4983230072969 + 3 ^ 40 * 4065187 * 2
def baseEnd_4065187 : Nat := 2087394881409091670867051

theorem tailTrace_4065187 : CollatzResearch.WordTrace tailWord_4065187 prefixEnd_4065187 2087394881409091670867051 := by
  unfold tailWord_4065187
  simp only [CollatzResearch.WordTrace]
  refine ⟨148269550723529252510361815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98846367149019501673574543 148269550723529252510361815)
  ·
    refine ⟨222404326085293878765542723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148269550723529252510361815 222404326085293878765542723)
    ·
      refine ⟨333606489127940818148314085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222404326085293878765542723 333606489127940818148314085)
      ·
        refine ⟨62551216711488903402808891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333606489127940818148314085 62551216711488903402808891)
        ·
          refine ⟨93826825067233355104213337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62551216711488903402808891 93826825067233355104213337)
          ·
            refine ⟨70370118800425016328160003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93826825067233355104213337 70370118800425016328160003)
            ·
              refine ⟨105555178200637524492240005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70370118800425016328160003 105555178200637524492240005)
              ·
                refine ⟨19791595912619535842295001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105555178200637524492240005 19791595912619535842295001)
                ·
                  refine ⟨14843696934464651881721251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19791595912619535842295001 14843696934464651881721251)
                  ·
                    refine ⟨22265545401696977822581877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14843696934464651881721251 22265545401696977822581877)
                    ·
                      refine ⟨2087394881409091670867051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22265545401696977822581877 2087394881409091670867051)
                      ·
                        rfl

theorem cell23_4065187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_4065187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065187 prefixEnd_4065187 := by exact prefixLift 4065187
  have htrace : WordTrace (prefixWord ++ tailWord_4065187) baseStart_4065187 baseEnd_4065187 := by
    simpa [prefixWord, tailWord_4065187, baseEnd_4065187] using wordTrace_append hprefix tailTrace_4065187
  have hstable : (prefixWord ++ tailWord_4065187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065187).length < 2 ^ (prefixWord ++ tailWord_4065187).sum := by decide
  have hdescent : baseEnd_4065187 < baseStart_4065187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065188 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_4065188 : Nat := 118140960795 + 4065188 * 2 ^ 59
def prefixEnd_4065188 : Nat := 4983230072969 + 3 ^ 40 * 4065188 * 2
def baseEnd_4065188 : Nat := 2087395394889746166954547

theorem tailTrace_4065188 : CollatzResearch.WordTrace tailWord_4065188 prefixEnd_4065188 2087395394889746166954547 := by
  unfold tailWord_4065188
  simp only [CollatzResearch.WordTrace]
  refine ⟨74134793598262814840574109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98846391464350419787432145 74134793598262814840574109)
  ·
    refine ⟨27800547599348555565215291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74134793598262814840574109 27800547599348555565215291)
    ·
      refine ⟨41700821399022833347822937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27800547599348555565215291 41700821399022833347822937)
      ·
        refine ⟨31275616049267125010867203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41700821399022833347822937 31275616049267125010867203)
        ·
          refine ⟨46913424073900687516300805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31275616049267125010867203 46913424073900687516300805)
          ·
            refine ⟨8796267013856378909306401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46913424073900687516300805 8796267013856378909306401)
            ·
              refine ⟨6597200260392284181979801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8796267013856378909306401 6597200260392284181979801)
              ·
                refine ⟨4947900195294213136484851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6597200260392284181979801 4947900195294213136484851)
                ·
                  refine ⟨7421850292941319704727277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947900195294213136484851 7421850292941319704727277)
                  ·
                    refine ⟨2783193859852994889272729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7421850292941319704727277 2783193859852994889272729)
                    ·
                      refine ⟨2087395394889746166954547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783193859852994889272729 2087395394889746166954547)
                      ·
                        rfl

theorem cell23_4065188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_4065188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065188 prefixEnd_4065188 := by exact prefixLift 4065188
  have htrace : WordTrace (prefixWord ++ tailWord_4065188) baseStart_4065188 baseEnd_4065188 := by
    simpa [prefixWord, tailWord_4065188, baseEnd_4065188] using wordTrace_append hprefix tailTrace_4065188
  have hstable : (prefixWord ++ tailWord_4065188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065188).length < 2 ^ (prefixWord ++ tailWord_4065188).sum := by decide
  have hdescent : baseEnd_4065188 < baseStart_4065188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065224 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 7]
def baseStart_4065224 : Nat := 118140960795 + 4065224 * 2 ^ 59
def prefixEnd_4065224 : Nat := 4983230072969 + 3 ^ 40 * 4065224 * 2
def baseEnd_4065224 : Nat := 231934875577034225122709

theorem tailTrace_4065224 : CollatzResearch.WordTrace tailWord_4065224 prefixEnd_4065224 231934875577034225122709 := by
  unfold tailWord_4065224
  simp only [CollatzResearch.WordTrace]
  refine ⟨74135450112197603914729363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98847266816263471886305817 74135450112197603914729363)
  ·
    refine ⟨111203175168296405872094045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74135450112197603914729363 111203175168296405872094045)
    ·
      refine ⟨41701190688111152202035267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111203175168296405872094045 41701190688111152202035267)
      ·
        refine ⟨62551786032166728303052901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41701190688111152202035267 62551786032166728303052901)
        ·
          refine ⟨11728459881031261556822419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62551786032166728303052901 11728459881031261556822419)
          ·
            refine ⟨17592689821546892335233629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11728459881031261556822419 17592689821546892335233629)
            ·
              refine ⟨6597258683080084625712611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17592689821546892335233629 6597258683080084625712611)
              ·
                refine ⟨9895888024620126938568917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597258683080084625712611 9895888024620126938568917)
                ·
                  refine ⟨231934875577034225122709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9895888024620126938568917 231934875577034225122709)
                  ·
                    rfl

theorem cell23_4065224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 7].length) (baseStart_4065224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065224 prefixEnd_4065224 := by exact prefixLift 4065224
  have htrace : WordTrace (prefixWord ++ tailWord_4065224) baseStart_4065224 baseEnd_4065224 := by
    simpa [prefixWord, tailWord_4065224, baseEnd_4065224] using wordTrace_append hprefix tailTrace_4065224
  have hstable : (prefixWord ++ tailWord_4065224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065224).length < 2 ^ (prefixWord ++ tailWord_4065224).sum := by decide
  have hdescent : baseEnd_4065224 < baseStart_4065224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065278 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_4065278 : Nat := 118140960795 + 4065278 * 2 ^ 59
def prefixEnd_4065278 : Nat := 4983230072969 + 3 ^ 40 * 4065278 * 2
def baseEnd_4065278 : Nat := 2087441608148650814829133

theorem tailTrace_4065278 : CollatzResearch.WordTrace tailWord_4065278 prefixEnd_4065278 2087441608148650814829133 := by
  unfold tailWord_4065278
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534108720774946881490561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98848579844133050034616325 18534108720774946881490561)
  ·
    refine ⟨13900581540581210161117921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18534108720774946881490561 13900581540581210161117921)
    ·
      refine ⟨10425436155435907620838441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13900581540581210161117921 10425436155435907620838441)
      ·
        refine ⟨7819077116576930715628831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10425436155435907620838441 7819077116576930715628831)
        ·
          refine ⟨11728615674865396073443247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7819077116576930715628831 11728615674865396073443247)
          ·
            refine ⟨17592923512298094110164871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11728615674865396073443247 17592923512298094110164871)
            ·
              refine ⟨26389385268447141165247307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17592923512298094110164871 26389385268447141165247307)
              ·
                refine ⟨39584077902670711747870961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26389385268447141165247307 39584077902670711747870961)
                ·
                  refine ⟨29688058427003033810903221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39584077902670711747870961 29688058427003033810903221)
                  ·
                    refine ⟨2783255477531534419772177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29688058427003033810903221 2783255477531534419772177)
                    ·
                      refine ⟨2087441608148650814829133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783255477531534419772177 2087441608148650814829133)
                      ·
                        rfl

theorem cell23_4065278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_4065278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065278 prefixEnd_4065278 := by exact prefixLift 4065278
  have htrace : WordTrace (prefixWord ++ tailWord_4065278) baseStart_4065278 baseEnd_4065278 := by
    simpa [prefixWord, tailWord_4065278, baseEnd_4065278] using wordTrace_append hprefix tailTrace_4065278
  have hstable : (prefixWord ++ tailWord_4065278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065278).length < 2 ^ (prefixWord ++ tailWord_4065278).sum := by decide
  have hdescent : baseEnd_4065278 < baseStart_4065278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065291 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 2, 4, 2]
def baseStart_4065291 : Nat := 118140960795 + 4065291 * 2 ^ 59
def prefixEnd_4065291 : Nat := 4983230072969 + 3 ^ 40 * 4065291 * 2
def baseEnd_4065291 : Nat := 2087448283397159263966573

theorem tailTrace_4065291 : CollatzResearch.WordTrace tailWord_4065291 prefixEnd_4065291 2087448283397159263966573 := by
  unfold tailWord_4065291
  simp only [CollatzResearch.WordTrace]
  refine ⟨148273343915152478272147727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98848895943434985514765151 148273343915152478272147727)
  ·
    refine ⟨222410015872728717408221591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148273343915152478272147727 222410015872728717408221591)
    ·
      refine ⟨333615023809093076112332387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222410015872728717408221591 333615023809093076112332387)
      ·
        refine ⟨500422535713639614168498581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333615023809093076112332387 500422535713639614168498581)
        ·
          refine ⟨23457306361576856914148371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 500422535713639614168498581 23457306361576856914148371)
          ·
            refine ⟨35185959542365285371222557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23457306361576856914148371 35185959542365285371222557)
            ·
              refine ⟨13194734828386982014208459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35185959542365285371222557 13194734828386982014208459)
              ·
                refine ⟨19792102242580473021312689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13194734828386982014208459 19792102242580473021312689)
                ·
                  refine ⟨14844076681935354765984517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19792102242580473021312689 14844076681935354765984517)
                  ·
                    refine ⟨2783264377862879018622097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14844076681935354765984517 2783264377862879018622097)
                    ·
                      refine ⟨2087448283397159263966573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783264377862879018622097 2087448283397159263966573)
                      ·
                        rfl

theorem cell23_4065291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 4, 2].length) (baseStart_4065291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065291 prefixEnd_4065291 := by exact prefixLift 4065291
  have htrace : WordTrace (prefixWord ++ tailWord_4065291) baseStart_4065291 baseEnd_4065291 := by
    simpa [prefixWord, tailWord_4065291, baseEnd_4065291] using wordTrace_append hprefix tailTrace_4065291
  have hstable : (prefixWord ++ tailWord_4065291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065291).length < 2 ^ (prefixWord ++ tailWord_4065291).sum := by decide
  have hdescent : baseEnd_4065291 < baseStart_4065291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065297 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 12]
def baseStart_4065297 : Nat := 118140960795 + 4065297 * 2 ^ 59
def prefixEnd_4065297 : Nat := 4983230072969 + 3 ^ 40 * 4065297 * 2
def baseEnd_4065297 : Nat := 231939040475676248943505

theorem tailTrace_4065297 : CollatzResearch.WordTrace tailWord_4065297 prefixEnd_4065297 231939040475676248943505 := by
  unfold tailWord_4065297
  simp only [CollatzResearch.WordTrace]
  refine ⟨148273562753130741296866145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98849041835420494197910763 148273562753130741296866145)
  ·
    refine ⟨111205172064848055972649609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148273562753130741296866145 111205172064848055972649609)
    ·
      refine ⟨83403879048636041979487207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111205172064848055972649609 83403879048636041979487207)
      ·
        refine ⟨125105818572954062969230811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83403879048636041979487207 125105818572954062969230811)
        ·
          refine ⟨187658727859431094453846217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125105818572954062969230811 187658727859431094453846217)
          ·
            refine ⟨140744045894573320840384663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187658727859431094453846217 140744045894573320840384663)
            ·
              refine ⟨211116068841859981260576995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140744045894573320840384663 211116068841859981260576995)
              ·
                refine ⟨316674103262789971890865493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211116068841859981260576995 316674103262789971890865493)
                ·
                  refine ⟨231939040475676248943505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 316674103262789971890865493 231939040475676248943505)
                  ·
                    rfl

theorem cell23_4065297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 12].length) (baseStart_4065297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065297 prefixEnd_4065297 := by exact prefixLift 4065297
  have htrace : WordTrace (prefixWord ++ tailWord_4065297) baseStart_4065297 baseEnd_4065297 := by
    simpa [prefixWord, tailWord_4065297, baseEnd_4065297] using wordTrace_append hprefix tailTrace_4065297
  have hstable : (prefixWord ++ tailWord_4065297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065297).length < 2 ^ (prefixWord ++ tailWord_4065297).sum := by decide
  have hdescent : baseEnd_4065297 < baseStart_4065297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065308 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_4065308 : Nat := 118140960795 + 4065308 * 2 ^ 59
def prefixEnd_4065308 : Nat := 4983230072969 + 3 ^ 40 * 4065308 * 2
def baseEnd_4065308 : Nat := 2087457012568285697453995

theorem tailTrace_4065308 : CollatzResearch.WordTrace tailWord_4065308 prefixEnd_4065308 2087457012568285697453995 := by
  unfold tailWord_4065308
  simp only [CollatzResearch.WordTrace]
  refine ⟨74136981978045445087758289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98849309304060593450344385 74136981978045445087758289)
  ·
    refine ⟨55602736483534083815818717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74136981978045445087758289 55602736483534083815818717)
    ·
      refine ⟨20851026181325281430932019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55602736483534083815818717 20851026181325281430932019)
      ·
        refine ⟨31276539271987922146398029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20851026181325281430932019 31276539271987922146398029)
        ·
          refine ⟨11728702226995470804899261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31276539271987922146398029 11728702226995470804899261)
          ·
            refine ⟨4398263335123301551837223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11728702226995470804899261 4398263335123301551837223)
            ·
              refine ⟨6597395002684952327755835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398263335123301551837223 6597395002684952327755835)
              ·
                refine ⟨9896092504027428491633753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597395002684952327755835 9896092504027428491633753)
                ·
                  refine ⟨7422069378020571368725315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9896092504027428491633753 7422069378020571368725315)
                  ·
                    refine ⟨11133104067030857053087973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7422069378020571368725315 11133104067030857053087973)
                    ·
                      refine ⟨2087457012568285697453995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11133104067030857053087973 2087457012568285697453995)
                      ·
                        rfl

theorem cell23_4065308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_4065308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065308 prefixEnd_4065308 := by exact prefixLift 4065308
  have htrace : WordTrace (prefixWord ++ tailWord_4065308) baseStart_4065308 baseEnd_4065308 := by
    simpa [prefixWord, tailWord_4065308, baseEnd_4065308] using wordTrace_append hprefix tailTrace_4065308
  have hstable : (prefixWord ++ tailWord_4065308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065308).length < 2 ^ (prefixWord ++ tailWord_4065308).sum := by decide
  have hdescent : baseEnd_4065308 < baseStart_4065308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065314 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 8]
def baseStart_4065314 : Nat := 118140960795 + 4065314 * 2 ^ 59
def prefixEnd_4065314 : Nat := 4983230072969 + 3 ^ 40 * 4065314 * 2
def baseEnd_4065314 : Nat := 231940010383579185997663

theorem tailTrace_4065314 : CollatzResearch.WordTrace tailWord_4065314 prefixEnd_4065314 231940010383579185997663 := by
  unfold tailWord_4065314
  simp only [CollatzResearch.WordTrace]
  refine ⟨37068545698517288300058749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98849455196046102133489997 37068545698517288300058749)
  ·
    refine ⟨13900704636943983112522031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37068545698517288300058749 13900704636943983112522031)
    ·
      refine ⟨20851056955415974668783047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13900704636943983112522031 20851056955415974668783047)
      ·
        refine ⟨31276585433123962003174571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20851056955415974668783047 31276585433123962003174571)
        ·
          refine ⟨46914878149685943004761857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31276585433123962003174571 46914878149685943004761857)
          ·
            refine ⟨35186158612264457253571393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46914878149685943004761857 35186158612264457253571393)
            ·
              refine ⟨26389618959198342940178545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35186158612264457253571393 26389618959198342940178545)
              ·
                refine ⟨19792214219398757205133909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26389618959198342940178545 19792214219398757205133909)
                ·
                  refine ⟨231940010383579185997663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19792214219398757205133909 231940010383579185997663)
                  ·
                    rfl

theorem cell23_4065314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_4065314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065314 prefixEnd_4065314 := by exact prefixLift 4065314
  have htrace : WordTrace (prefixWord ++ tailWord_4065314) baseStart_4065314 baseEnd_4065314 := by
    simpa [prefixWord, tailWord_4065314, baseEnd_4065314] using wordTrace_append hprefix tailTrace_4065314
  have hstable : (prefixWord ++ tailWord_4065314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065314).length < 2 ^ (prefixWord ++ tailWord_4065314).sum := by decide
  have hdescent : baseEnd_4065314 < baseStart_4065314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065351 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_4065351 : Nat := 118140960795 + 4065351 * 2 ^ 59
def prefixEnd_4065351 : Nat := 4983230072969 + 3 ^ 40 * 4065351 * 2
def baseEnd_4065351 : Nat := 2087479092236429029216297

theorem tailTrace_4065351 : CollatzResearch.WordTrace tailWord_4065351 prefixEnd_4065351 2087479092236429029216297 := by
  unfold tailWord_4065351
  simp only [CollatzResearch.WordTrace]
  refine ⟨148275532294935108519331907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98850354863290072346221271 148275532294935108519331907)
  ·
    refine ⟨222413298442402662778997861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148275532294935108519331907 222413298442402662778997861)
    ·
      refine ⟨41702493457950499271062099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222413298442402662778997861 41702493457950499271062099)
      ·
        refine ⟨62553740186925748906593149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41702493457950499271062099 62553740186925748906593149)
        ·
          refine ⟨23457652570097155839972431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62553740186925748906593149 23457652570097155839972431)
          ·
            refine ⟨35186478855145733759958647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23457652570097155839972431 35186478855145733759958647)
            ·
              refine ⟨52779718282718600639937971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35186478855145733759958647 52779718282718600639937971)
              ·
                refine ⟨79169577424077900959906957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52779718282718600639937971 79169577424077900959906957)
                ·
                  refine ⟨29688591534029212859965109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79169577424077900959906957 29688591534029212859965109)
                  ·
                    refine ⟨2783305456315238705621729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29688591534029212859965109 2783305456315238705621729)
                    ·
                      refine ⟨2087479092236429029216297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783305456315238705621729 2087479092236429029216297)
                      ·
                        rfl

theorem cell23_4065351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_4065351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065351 prefixEnd_4065351 := by exact prefixLift 4065351
  have htrace : WordTrace (prefixWord ++ tailWord_4065351) baseStart_4065351 baseEnd_4065351 := by
    simpa [prefixWord, tailWord_4065351, baseEnd_4065351] using wordTrace_append hprefix tailTrace_4065351
  have hstable : (prefixWord ++ tailWord_4065351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065351).length < 2 ^ (prefixWord ++ tailWord_4065351).sum := by decide
  have hdescent : baseEnd_4065351 < baseStart_4065351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065358 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_4065358 : Nat := 118140960795 + 4065358 * 2 ^ 59
def prefixEnd_4065358 : Nat := 4983230072969 + 3 ^ 40 * 4065358 * 2
def baseEnd_4065358 : Nat := 2087482686601010501828765

theorem tailTrace_4065358 : CollatzResearch.WordTrace tailWord_4065358 prefixEnd_4065358 2087482686601010501828765 := by
  unfold tailWord_4065358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534473450738718589354591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98850525070606499143224485 18534473450738718589354591)
  ·
    refine ⟨27801710176108077884031887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18534473450738718589354591 27801710176108077884031887)
    ·
      refine ⟨41702565264162116826047831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27801710176108077884031887 41702565264162116826047831)
      ·
        refine ⟨62553847896243175239071747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41702565264162116826047831 62553847896243175239071747)
        ·
          refine ⟨93830771844364762858607621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62553847896243175239071747 93830771844364762858607621)
          ·
            refine ⟨17593269720818393035988929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93830771844364762858607621 17593269720818393035988929)
            ·
              refine ⟨13194952290613794776991697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17593269720818393035988929 13194952290613794776991697)
              ·
                refine ⟨9896214217960346082743773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13194952290613794776991697 9896214217960346082743773)
                ·
                  refine ⟨3711080331735129781028915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9896214217960346082743773 3711080331735129781028915)
                  ·
                    refine ⟨5566620497602694671543373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3711080331735129781028915 5566620497602694671543373)
                    ·
                      refine ⟨2087482686601010501828765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5566620497602694671543373 2087482686601010501828765)
                      ·
                        rfl

theorem cell23_4065358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_4065358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065358 prefixEnd_4065358 := by exact prefixLift 4065358
  have htrace : WordTrace (prefixWord ++ tailWord_4065358) baseStart_4065358 baseEnd_4065358 := by
    simpa [prefixWord, tailWord_4065358, baseEnd_4065358] using wordTrace_append hprefix tailTrace_4065358
  have hstable : (prefixWord ++ tailWord_4065358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065358).length < 2 ^ (prefixWord ++ tailWord_4065358).sum := by decide
  have hdescent : baseEnd_4065358 < baseStart_4065358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065391 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 4, 4]
def baseStart_4065391 : Nat := 118140960795 + 4065391 * 2 ^ 59
def prefixEnd_4065391 : Nat := 4983230072969 + 3 ^ 40 * 4065391 * 2
def baseEnd_4065391 : Nat := 695833210487536290905371

theorem tailTrace_4065391 : CollatzResearch.WordTrace tailWord_4065391 prefixEnd_4065391 695833210487536290905371 := by
  unfold tailWord_4065391
  simp only [CollatzResearch.WordTrace]
  refine ⟨148276991214790195350788027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98851327476526796900525351 148276991214790195350788027)
  ·
    refine ⟨222415486822185293026182041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148276991214790195350788027 222415486822185293026182041)
    ·
      refine ⟨166811615116638969769636531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222415486822185293026182041 166811615116638969769636531)
      ·
        refine ⟨250217422674958454654454797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166811615116638969769636531 250217422674958454654454797)
        ·
          refine ⟨93831533503109420495420549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250217422674958454654454797 93831533503109420495420549)
          ·
            refine ⟨17593412531833016342891353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93831533503109420495420549 17593412531833016342891353)
            ·
              refine ⟨13195059398874762257168515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17593412531833016342891353 13195059398874762257168515)
              ·
                refine ⟨19792589098312143385752773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13195059398874762257168515 19792589098312143385752773)
                ·
                  refine ⟨3711110455933526884828645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19792589098312143385752773 3711110455933526884828645)
                  ·
                    refine ⟨695833210487536290905371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3711110455933526884828645 695833210487536290905371)
                    ·
                      rfl

theorem cell23_4065391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 4].length) (baseStart_4065391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065391 prefixEnd_4065391 := by exact prefixLift 4065391
  have htrace : WordTrace (prefixWord ++ tailWord_4065391) baseStart_4065391 baseEnd_4065391 := by
    simpa [prefixWord, tailWord_4065391, baseEnd_4065391] using wordTrace_append hprefix tailTrace_4065391
  have hstable : (prefixWord ++ tailWord_4065391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065391).length < 2 ^ (prefixWord ++ tailWord_4065391).sum := by decide
  have hdescent : baseEnd_4065391 < baseStart_4065391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065392 : List Nat := [2, 1, 1, 1, 5, 3, 3, 2, 1, 1, 3]
def baseStart_4065392 : Nat := 118140960795 + 4065392 * 2 ^ 59
def prefixEnd_4065392 : Nat := 4983230072969 + 3 ^ 40 * 4065392 * 2
def baseEnd_4065392 : Nat := 2087500144943263368803609

theorem tailTrace_4065392 : CollatzResearch.WordTrace tailWord_4065392 prefixEnd_4065392 2087500144943263368803609 := by
  unfold tailWord_4065392
  simp only [CollatzResearch.WordTrace]
  refine ⟨74138513843893286260787215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98851351791857715014382953 74138513843893286260787215)
  ·
    refine ⟨111207770765839929391180823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74138513843893286260787215 111207770765839929391180823)
    ·
      refine ⟨166811656148759894086771235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111207770765839929391180823 166811656148759894086771235)
      ·
        refine ⟨250217484223139841130156853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166811656148759894086771235 250217484223139841130156853)
        ·
          refine ⟨23457889145919360105952205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250217484223139841130156853 23457889145919360105952205)
          ·
            refine ⟨8796708429719760039732077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23457889145919360105952205 8796708429719760039732077)
            ·
              refine ⟨3298765661144910014899529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8796708429719760039732077 3298765661144910014899529)
              ·
                refine ⟨2474074245858682511174647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298765661144910014899529 2474074245858682511174647)
                ·
                  refine ⟨3711111368788023766761971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474074245858682511174647 3711111368788023766761971)
                  ·
                    refine ⟨5566667053182035650142957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3711111368788023766761971 5566667053182035650142957)
                    ·
                      refine ⟨2087500144943263368803609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5566667053182035650142957 2087500144943263368803609)
                      ·
                        rfl

theorem cell23_4065392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 1, 3].length) (baseStart_4065392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065392 prefixEnd_4065392 := by exact prefixLift 4065392
  have htrace : WordTrace (prefixWord ++ tailWord_4065392) baseStart_4065392 baseEnd_4065392 := by
    simpa [prefixWord, tailWord_4065392, baseEnd_4065392] using wordTrace_append hprefix tailTrace_4065392
  have hstable : (prefixWord ++ tailWord_4065392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065392).length < 2 ^ (prefixWord ++ tailWord_4065392).sum := by decide
  have hdescent : baseEnd_4065392 < baseStart_4065392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065401 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_4065401 : Nat := 118140960795 + 4065401 * 2 ^ 59
def prefixEnd_4065401 : Nat := 4983230072969 + 3 ^ 40 * 4065401 * 2
def baseEnd_4065401 : Nat := 2087504766269153833591067

theorem tailTrace_4065401 : CollatzResearch.WordTrace tailWord_4065401 prefixEnd_4065401 2087504766269153833591067 := by
  unfold tailWord_4065401
  simp only [CollatzResearch.WordTrace]
  refine ⟨148277355944753967058652057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98851570629835978039101371 148277355944753967058652057)
  ·
    refine ⟨111208016958565475293989043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148277355944753967058652057 111208016958565475293989043)
    ·
      refine ⟨166812025437848212940983565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111208016958565475293989043 166812025437848212940983565)
      ·
        refine ⟨62554509539193079852868837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166812025437848212940983565 62554509539193079852868837)
        ·
          refine ⟨11728970538598702472412907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62554509539193079852868837 11728970538598702472412907)
          ·
            refine ⟨17593455807898053708619361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11728970538598702472412907 17593455807898053708619361)
            ·
              refine ⟨13195091855923540281464521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17593455807898053708619361 13195091855923540281464521)
              ·
                refine ⟨9896318891942655211098391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13195091855923540281464521 9896318891942655211098391)
                ·
                  refine ⟨14844478337913982816647587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9896318891942655211098391 14844478337913982816647587)
                  ·
                    refine ⟨22266717506870974224971381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14844478337913982816647587 22266717506870974224971381)
                    ·
                      refine ⟨2087504766269153833591067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22266717506870974224971381 2087504766269153833591067)
                      ·
                        rfl

theorem cell23_4065401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_4065401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065401 prefixEnd_4065401 := by exact prefixLift 4065401
  have htrace : WordTrace (prefixWord ++ tailWord_4065401) baseStart_4065401 baseEnd_4065401 := by
    simpa [prefixWord, tailWord_4065401, baseEnd_4065401] using wordTrace_append hprefix tailTrace_4065401
  have hstable : (prefixWord ++ tailWord_4065401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065401).length < 2 ^ (prefixWord ++ tailWord_4065401).sum := by decide
  have hdescent : baseEnd_4065401 < baseStart_4065401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065404 : List Nat := [2, 2, 2, 1, 1, 4, 1, 10]
def baseStart_4065404 : Nat := 118140960795 + 4065404 * 2 ^ 59
def prefixEnd_4065404 : Nat := 4983230072969 + 3 ^ 40 * 4065404 * 2
def baseEnd_4065404 : Nat := 77315048396708048957539

theorem tailTrace_4065404 : CollatzResearch.WordTrace tailWord_4065404 prefixEnd_4065404 77315048396708048957539 := by
  unfold tailWord_4065404
  simp only [CollatzResearch.WordTrace]
  refine ⟨74138732681871549285505633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98851643575828732380674177 74138732681871549285505633)
  ·
    refine ⟨55604049511403661964129225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74138732681871549285505633 55604049511403661964129225)
    ·
      refine ⟨41703037133552746473096919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55604049511403661964129225 41703037133552746473096919)
      ·
        refine ⟨62554555700329119709645379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41703037133552746473096919 62554555700329119709645379)
        ·
          refine ⟨93831833550493679564468069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62554555700329119709645379 93831833550493679564468069)
          ·
            refine ⟨17593468790717564918337763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93831833550493679564468069 17593468790717564918337763)
            ·
              refine ⟨26390203186076347377506645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17593468790717564918337763 26390203186076347377506645)
              ·
                refine ⟨77315048396708048957539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26390203186076347377506645 77315048396708048957539)
                ·
                  rfl

theorem cell23_4065404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 10].length) (baseStart_4065404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065404 prefixEnd_4065404 := by exact prefixLift 4065404
  have htrace : WordTrace (prefixWord ++ tailWord_4065404) baseStart_4065404 baseEnd_4065404 := by
    simpa [prefixWord, tailWord_4065404, baseEnd_4065404] using wordTrace_append hprefix tailTrace_4065404
  have hstable : (prefixWord ++ tailWord_4065404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065404).length < 2 ^ (prefixWord ++ tailWord_4065404).sum := by decide
  have hdescent : baseEnd_4065404 < baseStart_4065404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065418 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_4065418 : Nat := 118140960795 + 4065418 * 2 ^ 59
def prefixEnd_4065418 : Nat := 4983230072969 + 3 ^ 40 * 4065418 * 2
def baseEnd_4065418 : Nat := 2087513495440280267078489

theorem tailTrace_4065418 : CollatzResearch.WordTrace tailWord_4065418 prefixEnd_4065418 2087513495440280267078489 := by
  unfold tailWord_4065418
  simp only [CollatzResearch.WordTrace]
  refine ⟨37069493996423094740505227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98851983990461585974680605 37069493996423094740505227)
  ·
    refine ⟨55604240994634642110757841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37069493996423094740505227 55604240994634642110757841)
    ·
      refine ⟨41703180745975981583068381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55604240994634642110757841 41703180745975981583068381)
      ·
        refine ⟨15638692779740993093650643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41703180745975981583068381 15638692779740993093650643)
        ·
          refine ⟨23458039169611489640475965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15638692779740993093650643 23458039169611489640475965)
          ·
            refine ⟨8796764688604308615178487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23458039169611489640475965 8796764688604308615178487)
            ·
              refine ⟨13195147032906462922767731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796764688604308615178487 13195147032906462922767731)
              ·
                refine ⟨19792720549359694384151597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13195147032906462922767731 19792720549359694384151597)
                ·
                  refine ⟨7422270206009885394056849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19792720549359694384151597 7422270206009885394056849)
                  ·
                    refine ⟨5566702654507414045542637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7422270206009885394056849 5566702654507414045542637)
                    ·
                      refine ⟨2087513495440280267078489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5566702654507414045542637 2087513495440280267078489)
                      ·
                        rfl

theorem cell23_4065418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_4065418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065418 prefixEnd_4065418 := by exact prefixLift 4065418
  have htrace : WordTrace (prefixWord ++ tailWord_4065418) baseStart_4065418 baseEnd_4065418 := by
    simpa [prefixWord, tailWord_4065418, baseEnd_4065418] using wordTrace_append hprefix tailTrace_4065418
  have hstable : (prefixWord ++ tailWord_4065418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065418).length < 2 ^ (prefixWord ++ tailWord_4065418).sum := by decide
  have hdescent : baseEnd_4065418 < baseStart_4065418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065438 : List Nat := [4, 3, 1, 1, 4, 10]
def baseStart_4065438 : Nat := 118140960795 + 4065438 * 2 ^ 59
def prefixEnd_4065438 : Nat := 4983230072969 + 3 ^ 40 * 4065438 * 2
def baseEnd_4065438 : Nat := 8590632777997408184479

theorem tailTrace_4065438 : CollatzResearch.WordTrace tailWord_4065438 prefixEnd_4065438 8590632777997408184479 := by
  unfold tailWord_4065438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534838180702490297218621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98852470297079948251832645 18534838180702490297218621)
  ·
    refine ⟨6950564317763433861456983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18534838180702490297218621 6950564317763433861456983)
    ·
      refine ⟨10425846476645150792185475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6950564317763433861456983 10425846476645150792185475)
      ·
        refine ⟨15638769714967726188278213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10425846476645150792185475 15638769714967726188278213)
        ·
          refine ⟨2932269321556448660302165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15638769714967726188278213 2932269321556448660302165)
          ·
            refine ⟨8590632777997408184479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2932269321556448660302165 8590632777997408184479)
            ·
              rfl

theorem cell23_4065438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 10].length) (baseStart_4065438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065438 prefixEnd_4065438 := by exact prefixLift 4065438
  have htrace : WordTrace (prefixWord ++ tailWord_4065438) baseStart_4065438 baseEnd_4065438 := by
    simpa [prefixWord, tailWord_4065438, baseEnd_4065438] using wordTrace_append hprefix tailTrace_4065438
  have hstable : (prefixWord ++ tailWord_4065438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065438).length < 2 ^ (prefixWord ++ tailWord_4065438).sum := by decide
  have hdescent : baseEnd_4065438 < baseStart_4065438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065458 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_4065458 : Nat := 118140960795 + 4065458 * 2 ^ 59
def prefixEnd_4065458 : Nat := 4983230072969 + 3 ^ 40 * 4065458 * 2
def baseEnd_4065458 : Nat := 2087534034666460110578305

theorem tailTrace_4065458 : CollatzResearch.WordTrace tailWord_4065458 prefixEnd_4065458 2087534034666460110578305 := by
  unfold tailWord_4065458
  simp only [CollatzResearch.WordTrace]
  refine ⟨37069858726386866448369257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98852956603698310528984685 37069858726386866448369257)
  ·
    refine ⟨27802394044790149836276943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37069858726386866448369257 27802394044790149836276943)
    ·
      refine ⟨41703591067185224754415415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27802394044790149836276943 41703591067185224754415415)
      ·
        refine ⟨62555386600777837131623123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41703591067185224754415415 62555386600777837131623123)
        ·
          refine ⟨93833079901166755697434685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62555386600777837131623123 93833079901166755697434685)
          ·
            refine ⟨35187404962937533386538007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93833079901166755697434685 35187404962937533386538007)
            ·
              refine ⟨52781107444406300079807011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35187404962937533386538007 52781107444406300079807011)
              ·
                refine ⟨79171661166609450119710517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52781107444406300079807011 79171661166609450119710517)
                ·
                  refine ⟨7422343234369635948722861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79171661166609450119710517 7422343234369635948722861)
                  ·
                    refine ⟨2783378712888613480771073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7422343234369635948722861 2783378712888613480771073)
                    ·
                      refine ⟨2087534034666460110578305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783378712888613480771073 2087534034666460110578305)
                      ·
                        rfl

theorem cell23_4065458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_4065458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065458 prefixEnd_4065458 := by exact prefixLift 4065458
  have htrace : WordTrace (prefixWord ++ tailWord_4065458) baseStart_4065458 baseEnd_4065458 := by
    simpa [prefixWord, tailWord_4065458, baseEnd_4065458] using wordTrace_append hprefix tailTrace_4065458
  have hstable : (prefixWord ++ tailWord_4065458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065458).length < 2 ^ (prefixWord ++ tailWord_4065458).sum := by decide
  have hdescent : baseEnd_4065458 < baseStart_4065458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065505 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_4065505 : Nat := 118140960795 + 4065505 * 2 ^ 59
def prefixEnd_4065505 : Nat := 4983230072969 + 3 ^ 40 * 4065505 * 2
def baseEnd_4065505 : Nat := 2087558168257221426690589

theorem tailTrace_4065505 : CollatzResearch.WordTrace tailWord_4065505 prefixEnd_4065505 2087558168257221426690589 := by
  unfold tailWord_4065505
  simp only [CollatzResearch.WordTrace]
  refine ⟨148281149136377192820437969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98854099424251461880291979 148281149136377192820437969)
  ·
    refine ⟨111210861852282894615328477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148281149136377192820437969 111210861852282894615328477)
    ·
      refine ⟨41704073194606085480748179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111210861852282894615328477 41704073194606085480748179)
      ·
        refine ⟨62556109791909128221122269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41704073194606085480748179 62556109791909128221122269)
        ·
          refine ⟨23458541171965923082920851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62556109791909128221122269 23458541171965923082920851)
          ·
            refine ⟨35187811757948884624381277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23458541171965923082920851 35187811757948884624381277)
            ·
              refine ⟨13195429409230831734142979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35187811757948884624381277 13195429409230831734142979)
              ·
                refine ⟨19793144113846247601214469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13195429409230831734142979 19793144113846247601214469)
                ·
                  refine ⟨3711214521346171425227713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19793144113846247601214469 3711214521346171425227713)
                  ·
                    refine ⟨2783410891009628568920785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3711214521346171425227713 2783410891009628568920785)
                    ·
                      refine ⟨2087558168257221426690589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783410891009628568920785 2087558168257221426690589)
                      ·
                        rfl

theorem cell23_4065505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_4065505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065505 prefixEnd_4065505 := by exact prefixLift 4065505
  have htrace : WordTrace (prefixWord ++ tailWord_4065505) baseStart_4065505 baseEnd_4065505 := by
    simpa [prefixWord, tailWord_4065505, baseEnd_4065505] using wordTrace_append hprefix tailTrace_4065505
  have hstable : (prefixWord ++ tailWord_4065505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065505).length < 2 ^ (prefixWord ++ tailWord_4065505).sum := by decide
  have hdescent : baseEnd_4065505 < baseStart_4065505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065522 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_4065522 : Nat := 118140960795 + 4065522 * 2 ^ 59
def prefixEnd_4065522 : Nat := 4983230072969 + 3 ^ 40 * 4065522 * 2
def baseEnd_4065522 : Nat := 2087566897428347860178011

theorem tailTrace_4065522 : CollatzResearch.WordTrace tailWord_4065522 prefixEnd_4065522 2087566897428347860178011 := by
  unfold tailWord_4065522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37070442294328901180951705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98854512784877069815871213 37070442294328901180951705)
  ·
    refine ⟨27802831720746675885713779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37070442294328901180951705 27802831720746675885713779)
    ·
      refine ⟨41704247581120013828570669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27802831720746675885713779 41704247581120013828570669)
      ·
        refine ⟨15639092842920005185714001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41704247581120013828570669 15639092842920005185714001)
        ·
          refine ⟨11729319632190003889285501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15639092842920005185714001 11729319632190003889285501)
          ·
            refine ⟨4398494862071251458482063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11729319632190003889285501 4398494862071251458482063)
            ·
              refine ⟨6597742293106877187723095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398494862071251458482063 6597742293106877187723095)
              ·
                refine ⟨9896613439660315781584643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597742293106877187723095 9896613439660315781584643)
                ·
                  refine ⟨14844920159490473672376965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9896613439660315781584643 14844920159490473672376965)
                  ·
                    refine ⟨2783422529904463813570681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14844920159490473672376965 2783422529904463813570681)
                    ·
                      refine ⟨2087566897428347860178011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783422529904463813570681 2087566897428347860178011)
                      ·
                        rfl

theorem cell23_4065522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_4065522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065522 prefixEnd_4065522 := by exact prefixLift 4065522
  have htrace : WordTrace (prefixWord ++ tailWord_4065522) baseStart_4065522 baseEnd_4065522 := by
    simpa [prefixWord, tailWord_4065522, baseEnd_4065522] using wordTrace_append hprefix tailTrace_4065522
  have hstable : (prefixWord ++ tailWord_4065522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065522).length < 2 ^ (prefixWord ++ tailWord_4065522).sum := by decide
  have hdescent : baseEnd_4065522 < baseStart_4065522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065545 : List Nat := [1, 2, 1, 1, 3, 6, 1, 3, 5]
def baseStart_4065545 : Nat := 118140960795 + 4065545 * 2 ^ 59
def prefixEnd_4065545 : Nat := 4983230072969 + 3 ^ 40 * 4065545 * 2
def baseEnd_4065545 : Nat := 231953189720377918910045

theorem tailTrace_4065545 : CollatzResearch.WordTrace tailWord_4065545 prefixEnd_4065545 231953189720377918910045 := by
  unfold tailWord_4065545
  simp only [CollatzResearch.WordTrace]
  refine ⟨148282608056232279651894089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98855072037488186434596059 148282608056232279651894089)
  ·
    refine ⟨111211956042174209738920567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148282608056232279651894089 111211956042174209738920567)
    ·
      refine ⟨166817934063261314608380851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111211956042174209738920567 166817934063261314608380851)
      ·
        refine ⟨250226901094891971912571277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166817934063261314608380851 250226901094891971912571277)
        ·
          refine ⟨93835087910584489467214229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250226901094891971912571277 93835087910584489467214229)
          ·
            refine ⟨4398519745808647943775667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93835087910584489467214229 4398519745808647943775667)
            ·
              refine ⟨6597779618712971915663501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398519745808647943775667 6597779618712971915663501)
              ·
                refine ⟨2474167357017364468373813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6597779618712971915663501 2474167357017364468373813)
                ·
                  refine ⟨231953189720377918910045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2474167357017364468373813 231953189720377918910045)
                  ·
                    rfl

theorem cell23_4065545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 5].length) (baseStart_4065545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065545 prefixEnd_4065545 := by exact prefixLift 4065545
  have htrace : WordTrace (prefixWord ++ tailWord_4065545) baseStart_4065545 baseEnd_4065545 := by
    simpa [prefixWord, tailWord_4065545, baseEnd_4065545] using wordTrace_append hprefix tailTrace_4065545
  have hstable : (prefixWord ++ tailWord_4065545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065545).length < 2 ^ (prefixWord ++ tailWord_4065545).sum := by decide
  have hdescent : baseEnd_4065545 < baseStart_4065545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065562 : List Nat := [3, 1, 1, 3, 4, 1, 3, 2, 5]
def baseStart_4065562 : Nat := 118140960795 + 4065562 * 2 ^ 59
def prefixEnd_4065562 : Nat := 4983230072969 + 3 ^ 40 * 4065562 * 2
def baseEnd_4065562 : Nat := 231954159628280855964203

theorem tailTrace_4065562 : CollatzResearch.WordTrace tailWord_4065562 prefixEnd_4065562 231954159628280855964203 := by
  unfold tailWord_4065562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37070807024292672888815735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98855485398113794370175293 37070807024292672888815735)
  ·
    refine ⟨55606210536439009333223603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37070807024292672888815735 55606210536439009333223603)
    ·
      refine ⟨83409315804658513999835405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55606210536439009333223603 83409315804658513999835405)
      ·
        refine ⟨31278493426746942749938277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83409315804658513999835405 31278493426746942749938277)
        ·
          refine ⟨5864717517515051765613427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31278493426746942749938277 5864717517515051765613427)
          ·
            refine ⟨8797076276272577648420141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864717517515051765613427 8797076276272577648420141)
            ·
              refine ⟨3298903603602216618157553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8797076276272577648420141 3298903603602216618157553)
              ·
                refine ⟨2474177702701662463618165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298903603602216618157553 2474177702701662463618165)
                ·
                  refine ⟨231954159628280855964203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2474177702701662463618165 231954159628280855964203)
                  ·
                    rfl

theorem cell23_4065562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_4065562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065562 prefixEnd_4065562 := by exact prefixLift 4065562
  have htrace : WordTrace (prefixWord ++ tailWord_4065562) baseStart_4065562 baseEnd_4065562 := by
    simpa [prefixWord, tailWord_4065562, baseEnd_4065562] using wordTrace_append hprefix tailTrace_4065562
  have hstable : (prefixWord ++ tailWord_4065562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065562).length < 2 ^ (prefixWord ++ tailWord_4065562).sum := by decide
  have hdescent : baseEnd_4065562 < baseStart_4065562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065568 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_4065568 : Nat := 118140960795 + 4065568 * 2 ^ 59
def prefixEnd_4065568 : Nat := 4983230072969 + 3 ^ 40 * 4065568 * 2
def baseEnd_4065568 : Nat := 2087590517538454680202799

theorem tailTrace_4065568 : CollatzResearch.WordTrace tailWord_4065568 prefixEnd_4065568 2087590517538454680202799 := by
  unfold tailWord_4065568
  simp only [CollatzResearch.WordTrace]
  refine ⟨74141723467574477289990679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98855631290099303053320905 74141723467574477289990679)
  ·
    refine ⟨111212585201361715934986019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74141723467574477289990679 111212585201361715934986019)
    ·
      refine ⟨166818877802042573902479029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111212585201361715934986019 166818877802042573902479029)
      ·
        refine ⟨15639269793941491303357409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166818877802042573902479029 15639269793941491303357409)
        ·
          refine ⟨11729452345456118477518057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15639269793941491303357409 11729452345456118477518057)
          ·
            refine ⟨8797089259092088858138543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11729452345456118477518057 8797089259092088858138543)
            ·
              refine ⟨13195633888638133287207815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8797089259092088858138543 13195633888638133287207815)
              ·
                refine ⟨19793450832957199930811723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13195633888638133287207815 19793450832957199930811723)
                ·
                  refine ⟨29690176249435799896217585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19793450832957199930811723 29690176249435799896217585)
                  ·
                    refine ⟨22267632187076849922163189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29690176249435799896217585 22267632187076849922163189)
                    ·
                      refine ⟨2087590517538454680202799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22267632187076849922163189 2087590517538454680202799)
                      ·
                        rfl

theorem cell23_4065568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_4065568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065568 prefixEnd_4065568 := by exact prefixLift 4065568
  have htrace : WordTrace (prefixWord ++ tailWord_4065568) baseStart_4065568 baseEnd_4065568 := by
    simpa [prefixWord, tailWord_4065568, baseEnd_4065568] using wordTrace_append hprefix tailTrace_4065568
  have hstable : (prefixWord ++ tailWord_4065568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065568).length < 2 ^ (prefixWord ++ tailWord_4065568).sum := by decide
  have hdescent : baseEnd_4065568 < baseStart_4065568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065591 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_4065591 : Nat := 118140960795 + 4065591 * 2 ^ 59
def prefixEnd_4065591 : Nat := 4983230072969 + 3 ^ 40 * 4065591 * 2
def baseEnd_4065591 : Nat := 2087602327593508090215193

theorem tailTrace_4065591 : CollatzResearch.WordTrace tailWord_4065591 prefixEnd_4065591 2087602327593508090215193 := by
  unfold tailWord_4065591
  simp only [CollatzResearch.WordTrace]
  refine ⟨148284285814065629508068627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98856190542710419672045751 148284285814065629508068627)
  ·
    refine ⟨222426428721098444262102941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148284285814065629508068627 222426428721098444262102941)
    ·
      refine ⟨83409910770411916598288603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222426428721098444262102941 83409910770411916598288603)
      ·
        refine ⟨125114866155617874897432905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83409910770411916598288603 125114866155617874897432905)
        ·
          refine ⟨93836149616713406173074679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125114866155617874897432905 93836149616713406173074679)
          ·
            refine ⟨140754224425070109259612019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93836149616713406173074679 140754224425070109259612019)
            ·
              refine ⟨211131336637605163889418029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140754224425070109259612019 211131336637605163889418029)
              ·
                refine ⟨79174251239101936458531761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211131336637605163889418029 79174251239101936458531761)
                ·
                  refine ⟨59380688429326452343898821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79174251239101936458531761 59380688429326452343898821)
                  ·
                    refine ⟨11133879080498709814481029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59380688429326452343898821 11133879080498709814481029)
                    ·
                      refine ⟨2087602327593508090215193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11133879080498709814481029 2087602327593508090215193)
                      ·
                        rfl

theorem cell23_4065591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_4065591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065591 prefixEnd_4065591 := by exact prefixLift 4065591
  have htrace : WordTrace (prefixWord ++ tailWord_4065591) baseStart_4065591 baseEnd_4065591 := by
    simpa [prefixWord, tailWord_4065591, baseEnd_4065591] using wordTrace_append hprefix tailTrace_4065591
  have hstable : (prefixWord ++ tailWord_4065591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065591).length < 2 ^ (prefixWord ++ tailWord_4065591).sum := by decide
  have hdescent : baseEnd_4065591 < baseStart_4065591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065618 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 6]
def baseStart_4065618 : Nat := 118140960795 + 4065618 * 2 ^ 59
def prefixEnd_4065618 : Nat := 4983230072969 + 3 ^ 40 * 4065618 * 2
def baseEnd_4065618 : Nat := 231957354619019942730841

theorem tailTrace_4065618 : CollatzResearch.WordTrace tailWord_4065618 prefixEnd_4065618 231957354619019942730841 := by
  unfold tailWord_4065618
  simp only [CollatzResearch.WordTrace]
  refine ⟨37071317646241953279825377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98856847056645208746201005 37071317646241953279825377)
  ·
    refine ⟨27803488234681464959869033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37071317646241953279825377 27803488234681464959869033)
    ·
      refine ⟨20852616176011098719901775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27803488234681464959869033 20852616176011098719901775)
      ·
        refine ⟨31278924264016648079852663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20852616176011098719901775 31278924264016648079852663)
        ·
          refine ⟨46918386396024972119778995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31278924264016648079852663 46918386396024972119778995)
          ·
            refine ⟨70377579594037458179668493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46918386396024972119778995 70377579594037458179668493)
            ·
              refine ⟨26391592347764046817375685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70377579594037458179668493 26391592347764046817375685)
              ·
                refine ⟨4948423565205758778257941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26391592347764046817375685 4948423565205758778257941)
                ·
                  refine ⟨231957354619019942730841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4948423565205758778257941 231957354619019942730841)
                  ·
                    rfl

theorem cell23_4065618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_4065618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065618 prefixEnd_4065618 := by exact prefixLift 4065618
  have htrace : WordTrace (prefixWord ++ tailWord_4065618) baseStart_4065618 baseEnd_4065618 := by
    simpa [prefixWord, tailWord_4065618, baseEnd_4065618] using wordTrace_append hprefix tailTrace_4065618
  have hstable : (prefixWord ++ tailWord_4065618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065618).length < 2 ^ (prefixWord ++ tailWord_4065618).sum := by decide
  have hdescent : baseEnd_4065618 < baseStart_4065618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065641 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_4065641 : Nat := 118140960795 + 4065641 * 2 ^ 59
def prefixEnd_4065641 : Nat := 4983230072969 + 3 ^ 40 * 4065641 * 2
def baseEnd_4065641 : Nat := 2087628001626232894589963

theorem tailTrace_4065641 : CollatzResearch.WordTrace tailWord_4065641 prefixEnd_4065641 2087628001626232894589963 := by
  unfold tailWord_4065641
  simp only [CollatzResearch.WordTrace]
  refine ⟨148286109463884488047388777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98857406309256325364925851 148286109463884488047388777)
  ·
    refine ⟨111214582097913366035541583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148286109463884488047388777 111214582097913366035541583)
    ·
      refine ⟨166821873146870049053312375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111214582097913366035541583 166821873146870049053312375)
      ·
        refine ⟨250232809720305073579968563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166821873146870049053312375 250232809720305073579968563)
        ·
          refine ⟨375349214580457610369952845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250232809720305073579968563 375349214580457610369952845)
          ·
            refine ⟨140755955467671603888732317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375349214580457610369952845 140755955467671603888732317)
            ·
              refine ⟨52783483300376851458274619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140755955467671603888732317 52783483300376851458274619)
              ·
                refine ⟨79175224950565277187411929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52783483300376851458274619 79175224950565277187411929)
                ·
                  refine ⟨59381418712923957890558947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79175224950565277187411929 59381418712923957890558947)
                  ·
                    refine ⟨89072128069385936835838421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59381418712923957890558947 89072128069385936835838421)
                    ·
                      refine ⟨2087628001626232894589963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89072128069385936835838421 2087628001626232894589963)
                      ·
                        rfl

theorem cell23_4065641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_4065641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065641 prefixEnd_4065641 := by exact prefixLift 4065641
  have htrace : WordTrace (prefixWord ++ tailWord_4065641) baseStart_4065641 baseEnd_4065641 := by
    simpa [prefixWord, tailWord_4065641, baseEnd_4065641] using wordTrace_append hprefix tailTrace_4065641
  have hstable : (prefixWord ++ tailWord_4065641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065641).length < 2 ^ (prefixWord ++ tailWord_4065641).sum := by decide
  have hdescent : baseEnd_4065641 < baseStart_4065641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065648 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 3, 5]
def baseStart_4065648 : Nat := 118140960795 + 4065648 * 2 ^ 59
def prefixEnd_4065648 : Nat := 4983230072969 + 3 ^ 40 * 4065648 * 2
def baseEnd_4065648 : Nat := 695877198663604789067477

theorem tailTrace_4065648 : CollatzResearch.WordTrace tailWord_4065648 prefixEnd_4065648 695877198663604789067477 := by
  unfold tailWord_4065648
  simp only [CollatzResearch.WordTrace]
  refine ⟨74143182387429564121446799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98857576516572752161929065 74143182387429564121446799)
  ·
    refine ⟨111214773581144346182170199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74143182387429564121446799 111214773581144346182170199)
    ·
      refine ⟨166822160371716519273255299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111214773581144346182170199 166822160371716519273255299)
      ·
        refine ⟨250233240557574778909882949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166822160371716519273255299 250233240557574778909882949)
        ·
          refine ⟨46918732604545271045603053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250233240557574778909882949 46918732604545271045603053)
          ·
            refine ⟨17594524726704476642101145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46918732604545271045603053 17594524726704476642101145)
            ·
              refine ⟨13195893545028357481575859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17594524726704476642101145 13195893545028357481575859)
              ·
                refine ⟨19793840317542536222363789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13195893545028357481575859 19793840317542536222363789)
                ·
                  refine ⟨7422690119078451083386421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19793840317542536222363789 7422690119078451083386421)
                  ·
                    refine ⟨695877198663604789067477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7422690119078451083386421 695877198663604789067477)
                    ·
                      rfl

theorem cell23_4065648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_4065648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065648 prefixEnd_4065648 := by exact prefixLift 4065648
  have htrace : WordTrace (prefixWord ++ tailWord_4065648) baseStart_4065648 baseEnd_4065648 := by
    simpa [prefixWord, tailWord_4065648, baseEnd_4065648] using wordTrace_append hprefix tailTrace_4065648
  have hstable : (prefixWord ++ tailWord_4065648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065648).length < 2 ^ (prefixWord ++ tailWord_4065648).sum := by decide
  have hdescent : baseEnd_4065648 < baseStart_4065648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065655 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 2, 3, 2]
def baseStart_4065655 : Nat := 118140960795 + 4065655 * 2 ^ 59
def prefixEnd_4065655 : Nat := 4983230072969 + 3 ^ 40 * 4065655 * 2
def baseEnd_4065655 : Nat := 2087635190355395839814899

theorem tailTrace_4065655 : CollatzResearch.WordTrace tailWord_4065655 prefixEnd_4065655 2087635190355395839814899 := by
  unfold tailWord_4065655
  simp only [CollatzResearch.WordTrace]
  refine ⟨148286620085833768438398419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98857746723889178958932279 148286620085833768438398419)
  ·
    refine ⟨222429930128750652657597629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148286620085833768438398419 222429930128750652657597629)
    ·
      refine ⟨83411223798281494746599111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222429930128750652657597629 83411223798281494746599111)
      ·
        refine ⟨125116835697422242119898667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83411223798281494746599111 125116835697422242119898667)
        ·
          refine ⟨187675253546133363179848001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125116835697422242119898667 187675253546133363179848001)
          ·
            refine ⟨140756440159600022384886001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187675253546133363179848001 140756440159600022384886001)
            ·
              refine ⟨105567330119700016788664501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140756440159600022384886001 105567330119700016788664501)
              ·
                refine ⟨9896937198721876573937297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105567330119700016788664501 9896937198721876573937297)
                ·
                  refine ⟨7422702899041407430452973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9896937198721876573937297 7422702899041407430452973)
                  ·
                    refine ⟨2783513587140527786419865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7422702899041407430452973 2783513587140527786419865)
                    ·
                      refine ⟨2087635190355395839814899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783513587140527786419865 2087635190355395839814899)
                      ·
                        rfl

theorem cell23_4065655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_4065655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065655 prefixEnd_4065655 := by exact prefixLift 4065655
  have htrace : WordTrace (prefixWord ++ tailWord_4065655) baseStart_4065655 baseEnd_4065655 := by
    simpa [prefixWord, tailWord_4065655, baseEnd_4065655] using wordTrace_append hprefix tailTrace_4065655
  have hstable : (prefixWord ++ tailWord_4065655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065655).length < 2 ^ (prefixWord ++ tailWord_4065655).sum := by decide
  have hdescent : baseEnd_4065655 < baseStart_4065655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065738 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 2, 7]
def baseStart_4065738 : Nat := 118140960795 + 4065738 * 2 ^ 59
def prefixEnd_4065738 : Nat := 4983230072969 + 3 ^ 40 * 4065738 * 2
def baseEnd_4065738 : Nat := 695892603083239671692339

theorem tailTrace_4065738 : CollatzResearch.WordTrace tailWord_4065738 prefixEnd_4065738 695892603083239671692339 := by
  unfold tailWord_4065738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37072411836133268403417467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98859764896355382409113245 37072411836133268403417467)
  ·
    refine ⟨55608617754199902605126201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37072411836133268403417467 55608617754199902605126201)
    ·
      refine ⟨41706463315649926953844651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55608617754199902605126201 41706463315649926953844651)
      ·
        refine ⟨62559694973474890430766977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41706463315649926953844651 62559694973474890430766977)
        ·
          refine ⟨46919771230106167823075233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62559694973474890430766977 46919771230106167823075233)
          ·
            refine ⟨35189828422579625867306425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46919771230106167823075233 35189828422579625867306425)
            ·
              refine ⟨26392371316934719400479819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35189828422579625867306425 26392371316934719400479819)
              ·
                refine ⟨39588556975402079100719729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26392371316934719400479819 39588556975402079100719729)
                ·
                  refine ⟨29691417731551559325539797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39588556975402079100719729 29691417731551559325539797)
                  ·
                    refine ⟨695892603083239671692339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29691417731551559325539797 695892603083239671692339)
                    ·
                      rfl

theorem cell23_4065738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_4065738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065738 prefixEnd_4065738 := by exact prefixLift 4065738
  have htrace : WordTrace (prefixWord ++ tailWord_4065738) baseStart_4065738 baseEnd_4065738 := by
    simpa [prefixWord, tailWord_4065738, baseEnd_4065738] using wordTrace_append hprefix tailTrace_4065738
  have hstable : (prefixWord ++ tailWord_4065738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065738).length < 2 ^ (prefixWord ++ tailWord_4065738).sum := by decide
  have hdescent : baseEnd_4065738 < baseStart_4065738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065779 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 1, 3, 2]
def baseStart_4065779 : Nat := 118140960795 + 4065779 * 2 ^ 59
def prefixEnd_4065779 : Nat := 4983230072969 + 3 ^ 40 * 4065779 * 2
def baseEnd_4065779 : Nat := 2087698861956553354664329

theorem tailTrace_4065779 : CollatzResearch.WordTrace tailWord_4065779 prefixEnd_4065779 2087698861956553354664329 := by
  unfold tailWord_4065779
  simp only [CollatzResearch.WordTrace]
  refine ⟨148291142737384537615912391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98860761824923025077274927 148291142737384537615912391)
  ·
    refine ⟨222436714106076806423868587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148291142737384537615912391 222436714106076806423868587)
    ·
      refine ⟨333655071159115209635802881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222436714106076806423868587 333655071159115209635802881)
      ·
        refine ⟨250241303369336407226852161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333655071159115209635802881 250241303369336407226852161)
        ·
          refine ⟨187680977527002305420139121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250241303369336407226852161 187680977527002305420139121)
          ·
            refine ⟨140760733145251729065104341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187680977527002305420139121 140760733145251729065104341)
            ·
              refine ⟨3299079683091837399963383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 140760733145251729065104341 3299079683091837399963383)
              ·
                refine ⟨4948619524637756099945075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3299079683091837399963383 4948619524637756099945075)
                ·
                  refine ⟨7422929286956634149917613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4948619524637756099945075 7422929286956634149917613)
                  ·
                    refine ⟨2783598482608737806219105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7422929286956634149917613 2783598482608737806219105)
                    ·
                      refine ⟨2087698861956553354664329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783598482608737806219105 2087698861956553354664329)
                      ·
                        rfl

theorem cell23_4065779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 3, 2].length) (baseStart_4065779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065779 prefixEnd_4065779 := by exact prefixLift 4065779
  have htrace : WordTrace (prefixWord ++ tailWord_4065779) baseStart_4065779 baseEnd_4065779 := by
    simpa [prefixWord, tailWord_4065779, baseEnd_4065779] using wordTrace_append hprefix tailTrace_4065779
  have hstable : (prefixWord ++ tailWord_4065779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065779).length < 2 ^ (prefixWord ++ tailWord_4065779).sum := by decide
  have hdescent : baseEnd_4065779 < baseStart_4065779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065788 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_4065788 : Nat := 118140960795 + 4065788 * 2 ^ 59
def prefixEnd_4065788 : Nat := 4983230072969 + 3 ^ 40 * 4065788 * 2
def baseEnd_4065788 : Nat := 2087703483282443819451787

theorem tailTrace_4065788 : CollatzResearch.WordTrace tailWord_4065788 prefixEnd_4065788 2087703483282443819451787 := by
  unfold tailWord_4065788
  simp only [CollatzResearch.WordTrace]
  refine ⟨74145735497175966076495009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98860980662901288101993345 74145735497175966076495009)
  ·
    refine ⟨55609301622881974557371257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74145735497175966076495009 55609301622881974557371257)
    ·
      refine ⟨41706976217161480918028443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55609301622881974557371257 41706976217161480918028443)
      ·
        refine ⟨62560464325742221377042665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41706976217161480918028443 62560464325742221377042665)
        ·
          refine ⟨46920348244306666032781999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62560464325742221377042665 46920348244306666032781999)
          ·
            refine ⟨70380522366459999049172999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46920348244306666032781999 70380522366459999049172999)
            ·
              refine ⟨105570783549689998573759499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70380522366459999049172999 105570783549689998573759499)
              ·
                refine ⟨158356175324534997860639249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105570783549689998573759499 158356175324534997860639249)
                ·
                  refine ⟨118767131493401248395479437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158356175324534997860639249 118767131493401248395479437)
                  ·
                    refine ⟨44537674310025468148304789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118767131493401248395479437 44537674310025468148304789)
                    ·
                      refine ⟨2087703483282443819451787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44537674310025468148304789 2087703483282443819451787)
                      ·
                        rfl

theorem cell23_4065788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_4065788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065788 prefixEnd_4065788 := by exact prefixLift 4065788
  have htrace : WordTrace (prefixWord ++ tailWord_4065788) baseStart_4065788 baseEnd_4065788 := by
    simpa [prefixWord, tailWord_4065788, baseEnd_4065788] using wordTrace_append hprefix tailTrace_4065788
  have hstable : (prefixWord ++ tailWord_4065788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065788).length < 2 ^ (prefixWord ++ tailWord_4065788).sum := by decide
  have hdescent : baseEnd_4065788 < baseStart_4065788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065825 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_4065825 : Nat := 118140960795 + 4065825 * 2 ^ 59
def prefixEnd_4065825 : Nat := 4983230072969 + 3 ^ 40 * 4065825 * 2
def baseEnd_4065825 : Nat := 2087722482066660174689117

theorem tailTrace_4065825 : CollatzResearch.WordTrace tailWord_4065825 prefixEnd_4065825 2087722482066660174689117 := by
  unfold tailWord_4065825
  simp only [CollatzResearch.WordTrace]
  refine ⟨148292820495217887472086929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98861880330145258314724619 148292820495217887472086929)
  ·
    refine ⟨111219615371413415604065197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148292820495217887472086929 111219615371413415604065197)
    ·
      refine ⟨41707355764280030851524449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111219615371413415604065197 41707355764280030851524449)
      ·
        refine ⟨31280516823210023138643337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41707355764280030851524449 31280516823210023138643337)
        ·
          refine ⟨23460387617407517353982503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31280516823210023138643337 23460387617407517353982503)
          ·
            refine ⟨35190581426111276030973755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23460387617407517353982503 35190581426111276030973755)
            ·
              refine ⟨52785872139166914046460633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35190581426111276030973755 52785872139166914046460633)
              ·
                refine ⟨39589404104375185534845475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52785872139166914046460633 39589404104375185534845475)
                ·
                  refine ⟨59384106156562778302268213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39589404104375185534845475 59384106156562778302268213)
                  ·
                    refine ⟨5567259952177760465837645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59384106156562778302268213 5567259952177760465837645)
                    ·
                      refine ⟨2087722482066660174689117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5567259952177760465837645 2087722482066660174689117)
                      ·
                        rfl

theorem cell23_4065825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_4065825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065825 prefixEnd_4065825 := by exact prefixLift 4065825
  have htrace : WordTrace (prefixWord ++ tailWord_4065825) baseStart_4065825 baseEnd_4065825 := by
    simpa [prefixWord, tailWord_4065825, baseEnd_4065825] using wordTrace_append hprefix tailTrace_4065825
  have hstable : (prefixWord ++ tailWord_4065825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065825).length < 2 ^ (prefixWord ++ tailWord_4065825).sum := by decide
  have hdescent : baseEnd_4065825 < baseStart_4065825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065837 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4065837 : Nat := 118140960795 + 4065837 * 2 ^ 59
def prefixEnd_4065837 : Nat := 4983230072969 + 3 ^ 40 * 4065837 * 2
def baseEnd_4065837 : Nat := 2087728643834514127739063

theorem tailTrace_4065837 : CollatzResearch.WordTrace tailWord_4065837 prefixEnd_4065837 2087728643834514127739063 := by
  unfold tailWord_4065837
  simp only [CollatzResearch.WordTrace]
  refine ⟨148293258171174413521523765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98862172114116275681015843 148293258171174413521523765)
  ·
    refine ⟨13902492953547601267642853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148293258171174413521523765 13902492953547601267642853)
    ·
      refine ⟨2606717428790175237683035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13902492953547601267642853 2606717428790175237683035)
      ·
        refine ⟨3910076143185262856524553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606717428790175237683035 3910076143185262856524553)
        ·
          refine ⟨2932557107388947142393415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3910076143185262856524553 2932557107388947142393415)
          ·
            refine ⟨4398835661083420713590123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2932557107388947142393415 4398835661083420713590123)
            ·
              refine ⟨6598253491625131070385185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398835661083420713590123 6598253491625131070385185)
              ·
                refine ⟨4948690118718848302788889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6598253491625131070385185 4948690118718848302788889)
                ·
                  refine ⟨3711517589039136227091667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4948690118718848302788889 3711517589039136227091667)
                  ·
                    refine ⟨5567276383558704340637501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3711517589039136227091667 5567276383558704340637501)
                    ·
                      refine ⟨2087728643834514127739063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5567276383558704340637501 2087728643834514127739063)
                      ·
                        rfl

theorem cell23_4065837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4065837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065837 prefixEnd_4065837 := by exact prefixLift 4065837
  have htrace : WordTrace (prefixWord ++ tailWord_4065837) baseStart_4065837 baseEnd_4065837 := by
    simpa [prefixWord, tailWord_4065837, baseEnd_4065837] using wordTrace_append hprefix tailTrace_4065837
  have hstable : (prefixWord ++ tailWord_4065837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065837).length < 2 ^ (prefixWord ++ tailWord_4065837).sum := by decide
  have hdescent : baseEnd_4065837 < baseStart_4065837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065845 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_4065845 : Nat := 118140960795 + 4065845 * 2 ^ 59
def prefixEnd_4065845 : Nat := 4983230072969 + 3 ^ 40 * 4065845 * 2
def baseEnd_4065845 : Nat := 695910917226583365479675

theorem tailTrace_4065845 : CollatzResearch.WordTrace tailWord_4065845 prefixEnd_4065845 695910917226583365479675 := by
  unfold tailWord_4065845
  simp only [CollatzResearch.WordTrace]
  refine ⟨148293549955145430887814989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98862366636763620591876659 148293549955145430887814989)
  ·
    refine ⟨55610081233179536582930621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148293549955145430887814989 55610081233179536582930621)
    ·
      refine ⟨20853780462442326218598983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55610081233179536582930621 20853780462442326218598983)
      ·
        refine ⟨31280670693663489327898475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20853780462442326218598983 31280670693663489327898475)
        ·
          refine ⟨46921006040495233991847713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31280670693663489327898475 46921006040495233991847713)
          ·
            refine ⟨35190754530371425493885785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46921006040495233991847713 35190754530371425493885785)
            ·
              refine ⟨26393065897778569120414339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35190754530371425493885785 26393065897778569120414339)
              ·
                refine ⟨39589598846667853680621509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26393065897778569120414339 39589598846667853680621509)
                ·
                  refine ⟨7423049783750222565116533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39589598846667853680621509 7423049783750222565116533)
                  ·
                    refine ⟨695910917226583365479675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7423049783750222565116533 695910917226583365479675)
                    ·
                      rfl

theorem cell23_4065845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_4065845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065845 prefixEnd_4065845 := by exact prefixLift 4065845
  have htrace : WordTrace (prefixWord ++ tailWord_4065845) baseStart_4065845 baseEnd_4065845 := by
    simpa [prefixWord, tailWord_4065845, baseEnd_4065845] using wordTrace_append hprefix tailTrace_4065845
  have hstable : (prefixWord ++ tailWord_4065845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065845).length < 2 ^ (prefixWord ++ tailWord_4065845).sum := by decide
  have hdescent : baseEnd_4065845 < baseStart_4065845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065860 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4065860 : Nat := 118140960795 + 4065860 * 2 ^ 59
def prefixEnd_4065860 : Nat := 4983230072969 + 3 ^ 40 * 4065860 * 2
def baseEnd_4065860 : Nat := 2087740453889567537751457

theorem tailTrace_4065860 : CollatzResearch.WordTrace tailWord_4065860 prefixEnd_4065860 2087740453889567537751457 := by
  unfold tailWord_4065860
  simp only [CollatzResearch.WordTrace]
  refine ⟨74147048525045544224805517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98862731366727392299740689 74147048525045544224805517)
  ·
    refine ⟨27805143196892079084302069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74147048525045544224805517 27805143196892079084302069)
    ·
      refine ⟨2606732174708632414153319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27805143196892079084302069 2606732174708632414153319)
      ·
        refine ⟨3910098262062948621229979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606732174708632414153319 3910098262062948621229979)
        ·
          refine ⟨5865147393094422931844969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910098262062948621229979 5865147393094422931844969)
          ·
            refine ⟨4398860544820817198883727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5865147393094422931844969 4398860544820817198883727)
            ·
              refine ⟨6598290817231225798325591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398860544820817198883727 6598290817231225798325591)
              ·
                refine ⟨9897436225846838697488387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6598290817231225798325591 9897436225846838697488387)
                ·
                  refine ⟨14846154338770258046232581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9897436225846838697488387 14846154338770258046232581)
                  ·
                    refine ⟨2783653938519423383668609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14846154338770258046232581 2783653938519423383668609)
                    ·
                      refine ⟨2087740453889567537751457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2783653938519423383668609 2087740453889567537751457)
                      ·
                        rfl

theorem cell23_4065860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4065860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065860 prefixEnd_4065860 := by exact prefixLift 4065860
  have htrace : WordTrace (prefixWord ++ tailWord_4065860) baseStart_4065860 baseEnd_4065860 := by
    simpa [prefixWord, tailWord_4065860, baseEnd_4065860] using wordTrace_append hprefix tailTrace_4065860
  have hstable : (prefixWord ++ tailWord_4065860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065860).length < 2 ^ (prefixWord ++ tailWord_4065860).sum := by decide
  have hdescent : baseEnd_4065860 < baseStart_4065860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065915 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 3]
def baseStart_4065915 : Nat := 118140960795 + 4065915 * 2 ^ 59
def prefixEnd_4065915 : Nat := 4983230072969 + 3 ^ 40 * 4065915 * 2
def baseEnd_4065915 : Nat := 2087768695325564822563703

theorem tailTrace_4065915 : CollatzResearch.WordTrace tailWord_4065915 prefixEnd_4065915 2087768695325564822563703 := by
  unfold tailWord_4065915
  simp only [CollatzResearch.WordTrace]
  refine ⟨148296103064891832842863199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98864068709927888561908799 148296103064891832842863199)
  ·
    refine ⟨222444154597337749264294799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148296103064891832842863199 222444154597337749264294799)
    ·
      refine ⟨333666231896006623896442199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222444154597337749264294799 333666231896006623896442199)
      ·
        refine ⟨500499347844009935844663299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333666231896006623896442199 500499347844009935844663299)
        ·
          refine ⟨750749021766014903766994949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500499347844009935844663299 750749021766014903766994949)
          ·
            refine ⟨140765441581127794456311553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 750749021766014903766994949 140765441581127794456311553)
            ·
              refine ⟨105574081185845845842233665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140765441581127794456311553 105574081185845845842233665)
              ·
                refine ⟨79180560889384384381675249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105574081185845845842233665 79180560889384384381675249)
                ·
                  refine ⟨59385420667038288286256437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79180560889384384381675249 59385420667038288286256437)
                  ·
                    refine ⟨5567383187534839526836541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59385420667038288286256437 5567383187534839526836541)
                    ·
                      refine ⟨2087768695325564822563703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5567383187534839526836541 2087768695325564822563703)
                      ·
                        rfl

theorem cell23_4065915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 3].length) (baseStart_4065915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065915 prefixEnd_4065915 := by exact prefixLift 4065915
  have htrace : WordTrace (prefixWord ++ tailWord_4065915) baseStart_4065915 baseEnd_4065915 := by
    simpa [prefixWord, tailWord_4065915, baseEnd_4065915] using wordTrace_append hprefix tailTrace_4065915
  have hstable : (prefixWord ++ tailWord_4065915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065915).length < 2 ^ (prefixWord ++ tailWord_4065915).sum := by decide
  have hdescent : baseEnd_4065915 < baseStart_4065915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065935 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 3, 5]
def baseStart_4065935 : Nat := 118140960795 + 4065935 * 2 ^ 59
def prefixEnd_4065935 : Nat := 4983230072969 + 3 ^ 40 * 4065935 * 2
def baseEnd_4065935 : Nat := 695926321646218248104537

theorem tailTrace_4065935 : CollatzResearch.WordTrace tailWord_4065935 prefixEnd_4065935 695926321646218248104537 := by
  unfold tailWord_4065935
  simp only [CollatzResearch.WordTrace]
  refine ⟨148296832524819376258591259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98864555016546250839060839 148296832524819376258591259)
  ·
    refine ⟨222445248787229064387886889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148296832524819376258591259 222445248787229064387886889)
    ·
      refine ⟨166833936590421798290915167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222445248787229064387886889 166833936590421798290915167)
      ·
        refine ⟨250250904885632697436372751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166833936590421798290915167 250250904885632697436372751)
        ·
          refine ⟨375376357328449046154559127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250250904885632697436372751 375376357328449046154559127)
          ·
            refine ⟨563064535992673569231838691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375376357328449046154559127 563064535992673569231838691)
            ·
              refine ⟨844596803989010353847758037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563064535992673569231838691 844596803989010353847758037)
              ·
                refine ⟨19795237593492430168306829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 844596803989010353847758037 19795237593492430168306829)
                ·
                  refine ⟨7423214097559661313115061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19795237593492430168306829 7423214097559661313115061)
                  ·
                    refine ⟨695926321646218248104537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7423214097559661313115061 695926321646218248104537)
                    ·
                      rfl

theorem cell23_4065935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 5].length) (baseStart_4065935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4065935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4065935 prefixEnd_4065935 := by exact prefixLift 4065935
  have htrace : WordTrace (prefixWord ++ tailWord_4065935) baseStart_4065935 baseEnd_4065935 := by
    simpa [prefixWord, tailWord_4065935, baseEnd_4065935] using wordTrace_append hprefix tailTrace_4065935
  have hstable : (prefixWord ++ tailWord_4065935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065935).length < 2 ^ (prefixWord ++ tailWord_4065935).sum := by decide
  have hdescent : baseEnd_4065935 < baseStart_4065935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066009 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 3]
def baseStart_4066009 : Nat := 118140960795 + 4066009 * 2 ^ 59
def prefixEnd_4066009 : Nat := 4983230072969 + 3 ^ 40 * 4066009 * 2
def baseEnd_4066009 : Nat := 2087816962507087454788271

theorem tailTrace_4066009 : CollatzResearch.WordTrace tailWord_4066009 prefixEnd_4066009 2087816962507087454788271 := by
  unfold tailWord_4066009
  simp only [CollatzResearch.WordTrace]
  refine ⟨148299531526551286896785081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98866354351034191264523387 148299531526551286896785081)
  ·
    refine ⟨111224648644913465172588811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148299531526551286896785081 111224648644913465172588811)
    ·
      refine ⟨166836972967370197758883217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111224648644913465172588811 166836972967370197758883217)
      ·
        refine ⟨125127729725527648319162413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166836972967370197758883217 125127729725527648319162413)
        ·
          refine ⟨46922898647072868119685905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125127729725527648319162413 46922898647072868119685905)
          ·
            refine ⟨35192173985304651089764429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46922898647072868119685905 35192173985304651089764429)
            ·
              refine ⟨13197065244489244158661661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35192173985304651089764429 13197065244489244158661661)
              ·
                refine ⟨4948899466683466559498123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13197065244489244158661661 4948899466683466559498123)
                ·
                  refine ⟨7423349200025199839247185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4948899466683466559498123 7423349200025199839247185)
                  ·
                    refine ⟨5567511900018899879435389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7423349200025199839247185 5567511900018899879435389)
                    ·
                      refine ⟨2087816962507087454788271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5567511900018899879435389 2087816962507087454788271)
                      ·
                        rfl

theorem cell23_4066009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_4066009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066009 prefixEnd_4066009 := by exact prefixLift 4066009
  have htrace : WordTrace (prefixWord ++ tailWord_4066009) baseStart_4066009 baseEnd_4066009 := by
    simpa [prefixWord, tailWord_4066009, baseEnd_4066009] using wordTrace_append hprefix tailTrace_4066009
  have hstable : (prefixWord ++ tailWord_4066009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066009).length < 2 ^ (prefixWord ++ tailWord_4066009).sum := by decide
  have hdescent : baseEnd_4066009 < baseStart_4066009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066025 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 1, 9]
def baseStart_4066025 : Nat := 118140960795 + 4066025 * 2 ^ 59
def prefixEnd_4066025 : Nat := 4983230072969 + 3 ^ 40 * 4066025 * 2
def baseEnd_4066025 : Nat := 695941726065853130729399

theorem tailTrace_4066025 : CollatzResearch.WordTrace tailWord_4066025 prefixEnd_4066025 695941726065853130729399 := by
  unfold tailWord_4066025
  simp only [CollatzResearch.WordTrace]
  refine ⟨148300115094493321629367529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98866743396328881086245019 148300115094493321629367529)
  ·
    refine ⟨111225086320869991222025647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148300115094493321629367529 111225086320869991222025647)
    ·
      refine ⟨166837629481304986833038471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111225086320869991222025647 166837629481304986833038471)
      ·
        refine ⟨250256444221957480249557707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166837629481304986833038471 250256444221957480249557707)
        ·
          refine ⟨375384666332936220374336561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250256444221957480249557707 375384666332936220374336561)
          ·
            refine ⟨281538499749702165280752421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375384666332936220374336561 281538499749702165280752421)
            ·
              refine ⟨52788468703069155990141079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281538499749702165280752421 52788468703069155990141079)
              ·
                refine ⟨79182703054603733985211619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52788468703069155990141079 79182703054603733985211619)
                ·
                  refine ⟨118774054581905600977817429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79182703054603733985211619 118774054581905600977817429)
                  ·
                    refine ⟨695941726065853130729399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 118774054581905600977817429 695941726065853130729399)
                    ·
                      rfl

theorem cell23_4066025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_4066025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066025 prefixEnd_4066025 := by exact prefixLift 4066025
  have htrace : WordTrace (prefixWord ++ tailWord_4066025) baseStart_4066025 baseEnd_4066025 := by
    simpa [prefixWord, tailWord_4066025, baseEnd_4066025] using wordTrace_append hprefix tailTrace_4066025
  have hstable : (prefixWord ++ tailWord_4066025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066025).length < 2 ^ (prefixWord ++ tailWord_4066025).sum := by decide
  have hdescent : baseEnd_4066025 < baseStart_4066025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066046 : List Nat := [4, 2, 2, 1, 2, 3, 2, 7]
def baseStart_4066046 : Nat := 118140960795 + 4066046 * 2 ^ 59
def prefixEnd_4066046 : Nat := 4983230072969 + 3 ^ 40 * 4066046 * 2
def baseEnd_4066046 : Nat := 77327257825603844815763

theorem tailTrace_4066046 : CollatzResearch.WordTrace tailWord_4066046 prefixEnd_4066046 77327257825603844815763 := by
  unfold tailWord_4066046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18537610128427155276985249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98867254018278161477254661 18537610128427155276985249)
  ·
    refine ⟨13903207596320366457738937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18537610128427155276985249 13903207596320366457738937)
    ·
      refine ⟨10427405697240274843304203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13903207596320366457738937 10427405697240274843304203)
      ·
        refine ⟨15641108545860412264956305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10427405697240274843304203 15641108545860412264956305)
        ·
          refine ⟨11730831409395309198717229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15641108545860412264956305 11730831409395309198717229)
          ·
            refine ⟨4399061778523240949518961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11730831409395309198717229 4399061778523240949518961)
            ·
              refine ⟨3299296333892430712139221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399061778523240949518961 3299296333892430712139221)
              ·
                refine ⟨77327257825603844815763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3299296333892430712139221 77327257825603844815763)
                ·
                  rfl

theorem cell23_4066046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_4066046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066046 prefixEnd_4066046 := by exact prefixLift 4066046
  have htrace : WordTrace (prefixWord ++ tailWord_4066046) baseStart_4066046 baseEnd_4066046 := by
    simpa [prefixWord, tailWord_4066046, baseEnd_4066046] using wordTrace_append hprefix tailTrace_4066046
  have hstable : (prefixWord ++ tailWord_4066046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066046).length < 2 ^ (prefixWord ++ tailWord_4066046).sum := by decide
  have hdescent : baseEnd_4066046 < baseStart_4066046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066052 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4066052 : Nat := 118140960795 + 4066052 * 2 ^ 59
def prefixEnd_4066052 : Nat := 4983230072969 + 3 ^ 40 * 4066052 * 2
def baseEnd_4066052 : Nat := 2087839042175230786550573

theorem tailTrace_4066052 : CollatzResearch.WordTrace tailWord_4066052 prefixEnd_4066052 2087839042175230786550573 := by
  unfold tailWord_4066052
  simp only [CollatzResearch.WordTrace]
  refine ⟨74150549932697752620300205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98867399910263670160400273 74150549932697752620300205)
  ·
    refine ⟨27806456224761657232612577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74150549932697752620300205 27806456224761657232612577)
    ·
      refine ⟨20854842168571242924459433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27806456224761657232612577 20854842168571242924459433)
      ·
        refine ⟨15641131626428432193344575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20854842168571242924459433 15641131626428432193344575)
        ·
          refine ⟨23461697439642648290016863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15641131626428432193344575 23461697439642648290016863)
          ·
            refine ⟨35192546159463972435025295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23461697439642648290016863 35192546159463972435025295)
            ·
              refine ⟨52788819239195958652537943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35192546159463972435025295 52788819239195958652537943)
              ·
                refine ⟨79183228858793937978806915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52788819239195958652537943 79183228858793937978806915)
                ·
                  refine ⟨118774843288190906968210373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79183228858793937978806915 118774843288190906968210373)
                  ·
                    refine ⟨22270283116535795056539445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118774843288190906968210373 22270283116535795056539445)
                    ·
                      refine ⟨2087839042175230786550573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22270283116535795056539445 2087839042175230786550573)
                      ·
                        rfl

theorem cell23_4066052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4066052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066052 prefixEnd_4066052 := by exact prefixLift 4066052
  have htrace : WordTrace (prefixWord ++ tailWord_4066052) baseStart_4066052 baseEnd_4066052 := by
    simpa [prefixWord, tailWord_4066052, baseEnd_4066052] using wordTrace_append hprefix tailTrace_4066052
  have hstable : (prefixWord ++ tailWord_4066052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066052).length < 2 ^ (prefixWord ++ tailWord_4066052).sum := by decide
  have hdescent : baseEnd_4066052 < baseStart_4066052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066062 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_4066062 : Nat := 118140960795 + 4066062 * 2 ^ 59
def prefixEnd_4066062 : Nat := 4983230072969 + 3 ^ 40 * 4066062 * 2
def baseEnd_4066062 : Nat := 2087844176981775747425527

theorem tailTrace_4066062 : CollatzResearch.WordTrace tailWord_4066062 prefixEnd_4066062 2087844176981775747425527 := by
  unfold tailWord_4066062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18537683074419909618558055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98867643063572851298976293 18537683074419909618558055)
  ·
    refine ⟨27806524611629864427837083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18537683074419909618558055 27806524611629864427837083)
    ·
      refine ⟨41709786917444796641755625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27806524611629864427837083 41709786917444796641755625)
      ·
        refine ⟨31282340188083597481316719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41709786917444796641755625 31282340188083597481316719)
        ·
          refine ⟨46923510282125396221975079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31282340188083597481316719 46923510282125396221975079)
          ·
            refine ⟨70385265423188094332962619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46923510282125396221975079 70385265423188094332962619)
            ·
              refine ⟨105577898134782141499443929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70385265423188094332962619 105577898134782141499443929)
              ·
                refine ⟨79183423601086606124582947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105577898134782141499443929 79183423601086606124582947)
                ·
                  refine ⟨118775135401629909186874421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79183423601086606124582947 118775135401629909186874421)
                  ·
                    refine ⟨11135168943902803986269477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118775135401629909186874421 11135168943902803986269477)
                    ·
                      refine ⟨2087844176981775747425527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11135168943902803986269477 2087844176981775747425527)
                      ·
                        rfl

theorem cell23_4066062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_4066062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066062 prefixEnd_4066062 := by exact prefixLift 4066062
  have htrace : WordTrace (prefixWord ++ tailWord_4066062) baseStart_4066062 baseEnd_4066062 := by
    simpa [prefixWord, tailWord_4066062, baseEnd_4066062] using wordTrace_append hprefix tailTrace_4066062
  have hstable : (prefixWord ++ tailWord_4066062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066062).length < 2 ^ (prefixWord ++ tailWord_4066062).sum := by decide
  have hdescent : baseEnd_4066062 < baseStart_4066062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066090 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4066090 : Nat := 118140960795 + 4066090 * 2 ^ 59
def prefixEnd_4066090 : Nat := 4983230072969 + 3 ^ 40 * 4066090 * 2
def baseEnd_4066090 : Nat := 2087858554440101637875399

theorem tailTrace_4066090 : CollatzResearch.WordTrace tailWord_4066090 prefixEnd_4066090 2087858554440101637875399 := by
  unfold tailWord_4066090
  simp only [CollatzResearch.WordTrace]
  refine ⟨37075621459814459432620931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98868323892838558486989149 37075621459814459432620931)
  ·
    refine ⟨55613432189721689148931397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37075621459814459432620931 55613432189721689148931397)
    ·
      refine ⟨10427518535572816715424637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55613432189721689148931397 10427518535572816715424637)
      ·
        refine ⟨3910319450839806268284239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10427518535572816715424637 3910319450839806268284239)
        ·
          refine ⟨5865479176259709402426359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910319450839806268284239 5865479176259709402426359)
          ·
            refine ⟨8798218764389564103639539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865479176259709402426359 8798218764389564103639539)
            ·
              refine ⟨13197328146584346155459309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798218764389564103639539 13197328146584346155459309)
              ·
                refine ⟨4948998054969129808297241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13197328146584346155459309 4948998054969129808297241)
                ·
                  refine ⟨3711748541226847356222931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4948998054969129808297241 3711748541226847356222931)
                  ·
                    refine ⟨5567622811840271034334397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3711748541226847356222931 5567622811840271034334397)
                    ·
                      refine ⟨2087858554440101637875399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5567622811840271034334397 2087858554440101637875399)
                      ·
                        rfl

theorem cell23_4066090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4066090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066090 prefixEnd_4066090 := by exact prefixLift 4066090
  have htrace : WordTrace (prefixWord ++ tailWord_4066090) baseStart_4066090 baseEnd_4066090 := by
    simpa [prefixWord, tailWord_4066090, baseEnd_4066090] using wordTrace_append hprefix tailTrace_4066090
  have hstable : (prefixWord ++ tailWord_4066090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066090).length < 2 ^ (prefixWord ++ tailWord_4066090).sum := by decide
  have hdescent : baseEnd_4066090 < baseStart_4066090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066092 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_4066092 : Nat := 118140960795 + 4066092 * 2 ^ 59
def prefixEnd_4066092 : Nat := 4983230072969 + 3 ^ 40 * 4066092 * 2
def baseEnd_4066092 : Nat := 2087859581401410630050389

theorem tailTrace_4066092 : CollatzResearch.WordTrace tailWord_4066092 prefixEnd_4066092 2087859581401410630050389 := by
  unfold tailWord_4066092
  simp only [CollatzResearch.WordTrace]
  refine ⟨74151279392625296036028265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98868372523500394714704353 74151279392625296036028265)
  ·
    refine ⟨55613459544468972027021199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74151279392625296036028265 55613459544468972027021199)
    ·
      refine ⟨83420189316703458040531799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55613459544468972027021199 83420189316703458040531799)
      ·
        refine ⟨125130283975055187060797699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83420189316703458040531799 125130283975055187060797699)
        ·
          refine ⟨187695425962582780591196549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125130283975055187060797699 187695425962582780591196549)
          ·
            refine ⟨35192892367984271360849353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187695425962582780591196549 35192892367984271360849353)
            ·
              refine ⟨26394669275988203520637015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35192892367984271360849353 26394669275988203520637015)
              ·
                refine ⟨39592003913982305280955523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26394669275988203520637015 39592003913982305280955523)
                ·
                  refine ⟨59388005870973457921433285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39592003913982305280955523 59388005870973457921433285)
                  ·
                    refine ⟨11135251100807523360268741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59388005870973457921433285 11135251100807523360268741)
                    ·
                      refine ⟨2087859581401410630050389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11135251100807523360268741 2087859581401410630050389)
                      ·
                        rfl

theorem cell23_4066092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_4066092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066092 prefixEnd_4066092 := by exact prefixLift 4066092
  have htrace : WordTrace (prefixWord ++ tailWord_4066092) baseStart_4066092 baseEnd_4066092 := by
    simpa [prefixWord, tailWord_4066092, baseEnd_4066092] using wordTrace_append hprefix tailTrace_4066092
  have hstable : (prefixWord ++ tailWord_4066092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066092).length < 2 ^ (prefixWord ++ tailWord_4066092).sum := by decide
  have hdescent : baseEnd_4066092 < baseStart_4066092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066119 : List Nat := [1, 1, 4, 1, 2, 1, 1, 7, 5]
def baseStart_4066119 : Nat := 118140960795 + 4066119 * 2 ^ 59
def prefixEnd_4066119 : Nat := 4983230072969 + 3 ^ 40 * 4066119 * 2
def baseEnd_4066119 : Nat := 231985938375453558268085

theorem tailTrace_4066119 : CollatzResearch.WordTrace tailWord_4066119 prefixEnd_4066119 231985938375453558268085 := by
  unfold tailWord_4066119
  simp only [CollatzResearch.WordTrace]
  refine ⟨148303543556152775683289411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98869029037435183788859607 148303543556152775683289411)
  ·
    refine ⟨222455315334229163524934117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148303543556152775683289411 222455315334229163524934117)
    ·
      refine ⟨41710371625167968160925147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222455315334229163524934117 41710371625167968160925147)
      ·
        refine ⟨62565557437751952241387721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41710371625167968160925147 62565557437751952241387721)
        ·
          refine ⟨46924168078313964181040791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62565557437751952241387721 46924168078313964181040791)
          ·
            refine ⟨70386252117470946271561187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46924168078313964181040791 70386252117470946271561187)
            ·
              refine ⟨105579378176206419407341781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70386252117470946271561187 105579378176206419407341781)
              ·
                refine ⟨2474516676004837954859573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105579378176206419407341781 2474516676004837954859573)
                ·
                  refine ⟨231985938375453558268085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2474516676004837954859573 231985938375453558268085)
                  ·
                    rfl

theorem cell23_4066119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 5].length) (baseStart_4066119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066119 prefixEnd_4066119 := by exact prefixLift 4066119
  have htrace : WordTrace (prefixWord ++ tailWord_4066119) baseStart_4066119 baseEnd_4066119 := by
    simpa [prefixWord, tailWord_4066119, baseEnd_4066119] using wordTrace_append hprefix tailTrace_4066119
  have hstable : (prefixWord ++ tailWord_4066119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066119).length < 2 ^ (prefixWord ++ tailWord_4066119).sum := by decide
  have hdescent : baseEnd_4066119 < baseStart_4066119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066166 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_4066166 : Nat := 118140960795 + 4066166 * 2 ^ 59
def prefixEnd_4066166 : Nat := 4983230072969 + 3 ^ 40 * 4066166 * 2
def baseEnd_4066166 : Nat := 695965859656614446841683

theorem tailTrace_4066166 : CollatzResearch.WordTrace tailWord_4066166 prefixEnd_4066166 695965859656614446841683 := by
  unfold tailWord_4066166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9269078611686406419390647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98870171857988335140166901 9269078611686406419390647)
  ·
    refine ⟨13903617917529609629085971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9269078611686406419390647 13903617917529609629085971)
    ·
      refine ⟨20855426876294414443628957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13903617917529609629085971 20855426876294414443628957)
      ·
        refine ⟨7820785078610405416360859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20855426876294414443628957 7820785078610405416360859)
        ·
          refine ⟨11731177617915608124541289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7820785078610405416360859 11731177617915608124541289)
          ·
            refine ⟨8798383213436706093405967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11731177617915608124541289 8798383213436706093405967)
            ·
              refine ⟨13197574820155059140108951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798383213436706093405967 13197574820155059140108951)
              ·
                refine ⟨19796362230232588710163427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13197574820155059140108951 19796362230232588710163427)
                ·
                  refine ⟨29694543345348883065245141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19796362230232588710163427 29694543345348883065245141)
                  ·
                    refine ⟨695965859656614446841683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29694543345348883065245141 695965859656614446841683)
                    ·
                      rfl

theorem cell23_4066166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_4066166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066166 prefixEnd_4066166 := by exact prefixLift 4066166
  have htrace : WordTrace (prefixWord ++ tailWord_4066166) baseStart_4066166 baseEnd_4066166 := by
    simpa [prefixWord, tailWord_4066166, baseEnd_4066166] using wordTrace_append hprefix tailTrace_4066166
  have hstable : (prefixWord ++ tailWord_4066166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066166).length < 2 ^ (prefixWord ++ tailWord_4066166).sum := by decide
  have hdescent : baseEnd_4066166 < baseStart_4066166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066169 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_4066169 : Nat := 118140960795 + 4066169 * 2 ^ 59
def prefixEnd_4066169 : Nat := 4983230072969 + 3 ^ 40 * 4066169 * 2
def baseEnd_4066169 : Nat := 2087899119411806828787535

theorem tailTrace_4066169 : CollatzResearch.WordTrace tailWord_4066169 prefixEnd_4066169 2087899119411806828787535 := by
  unfold tailWord_4066169
  simp only [CollatzResearch.WordTrace]
  refine ⟨148305367205971634222609561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98870244803981089481739707 148305367205971634222609561)
  ·
    refine ⟨111229025404478725666957171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148305367205971634222609561 111229025404478725666957171)
    ·
      refine ⟨166843538106718088500435757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111229025404478725666957171 166843538106718088500435757)
      ·
        refine ⟨62566326790019283187663409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166843538106718088500435757 62566326790019283187663409)
        ·
          refine ⟨46924745092514462390747557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62566326790019283187663409 46924745092514462390747557)
          ·
            refine ⟨8798389704846461698265167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46924745092514462390747557 8798389704846461698265167)
            ·
              refine ⟨13197584557269692547397751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8798389704846461698265167 13197584557269692547397751)
              ·
                refine ⟨19796376835904538821096627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13197584557269692547397751 19796376835904538821096627)
                ·
                  refine ⟨29694565253856808231644941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19796376835904538821096627 29694565253856808231644941)
                  ·
                    refine ⟨11135461970196303086866853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29694565253856808231644941 11135461970196303086866853)
                    ·
                      refine ⟨2087899119411806828787535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11135461970196303086866853 2087899119411806828787535)
                      ·
                        rfl

theorem cell23_4066169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_4066169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066169 prefixEnd_4066169 := by exact prefixLift 4066169
  have htrace : WordTrace (prefixWord ++ tailWord_4066169) baseStart_4066169 baseEnd_4066169 := by
    simpa [prefixWord, tailWord_4066169, baseEnd_4066169] using wordTrace_append hprefix tailTrace_4066169
  have hstable : (prefixWord ++ tailWord_4066169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066169).length < 2 ^ (prefixWord ++ tailWord_4066169).sum := by decide
  have hdescent : baseEnd_4066169 < baseStart_4066169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066179 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 5, 4]
def baseStart_4066179 : Nat := 118140960795 + 4066179 * 2 ^ 59
def prefixEnd_4066179 : Nat := 4983230072969 + 3 ^ 40 * 4066179 * 2
def baseEnd_4066179 : Nat := 695968084739450596554163

theorem tailTrace_4066179 : CollatzResearch.WordTrace tailWord_4066179 prefixEnd_4066179 695968084739450596554163 := by
  unfold tailWord_4066179
  simp only [CollatzResearch.WordTrace]
  refine ⟨148305731935935405930473591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98870487957290270620315727 148305731935935405930473591)
  ·
    refine ⟨222458597903903108895710387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148305731935935405930473591 222458597903903108895710387)
    ·
      refine ⟨333687896855854663343565581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222458597903903108895710387 333687896855854663343565581)
      ·
        refine ⟨125132961320945498753837093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333687896855854663343565581 125132961320945498753837093)
        ·
          refine ⟨23462430247677281016344455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125132961320945498753837093 23462430247677281016344455)
          ·
            refine ⟨35193645371515921524516683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23462430247677281016344455 35193645371515921524516683)
            ·
              refine ⟨52790468057273882286775025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35193645371515921524516683 52790468057273882286775025)
              ·
                refine ⟨39592851042955411715081269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52790468057273882286775025 39592851042955411715081269)
                ·
                  refine ⟨3711829785277069848288869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39592851042955411715081269 3711829785277069848288869)
                  ·
                    refine ⟨695968084739450596554163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3711829785277069848288869 695968084739450596554163)
                    ·
                      rfl

theorem cell23_4066179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 4].length) (baseStart_4066179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066179 prefixEnd_4066179 := by exact prefixLift 4066179
  have htrace : WordTrace (prefixWord ++ tailWord_4066179) baseStart_4066179 baseEnd_4066179 := by
    simpa [prefixWord, tailWord_4066179, baseEnd_4066179] using wordTrace_append hprefix tailTrace_4066179
  have hstable : (prefixWord ++ tailWord_4066179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066179).length < 2 ^ (prefixWord ++ tailWord_4066179).sum := by decide
  have hdescent : baseEnd_4066179 < baseStart_4066179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066276 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_4066276 : Nat := 118140960795 + 4066276 * 2 ^ 59
def prefixEnd_4066276 : Nat := 4983230072969 + 3 ^ 40 * 4066276 * 2
def baseEnd_4066276 : Nat := 2087954061841837910149543

theorem tailTrace_4066276 : CollatzResearch.WordTrace tailWord_4066276 prefixEnd_4066276 2087954061841837910149543 := by
  unfold tailWord_4066276
  simp only [CollatzResearch.WordTrace]
  refine ⟨74154634908291995748377341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98872846544389327664503121 74154634908291995748377341)
  ·
    refine ⟨27807988090609498405641503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74154634908291995748377341 27807988090609498405641503)
    ·
      refine ⟨41711982135914247608462255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27807988090609498405641503 41711982135914247608462255)
      ·
        refine ⟨62567973203871371412693383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41711982135914247608462255 62567973203871371412693383)
        ·
          refine ⟨93851959805807057119040075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62567973203871371412693383 93851959805807057119040075)
          ·
            refine ⟨140777939708710585678560113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93851959805807057119040075 140777939708710585678560113)
            ·
              refine ⟨105583454781532939258920085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140777939708710585678560113 105583454781532939258920085)
              ·
                refine ⟨4949224442884356527761879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105583454781532939258920085 4949224442884356527761879)
                ·
                  refine ⟨7423836664326534791642819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4949224442884356527761879 7423836664326534791642819)
                  ·
                    refine ⟨11135754996489802187464229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7423836664326534791642819 11135754996489802187464229)
                    ·
                      refine ⟨2087954061841837910149543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11135754996489802187464229 2087954061841837910149543)
                      ·
                        rfl

theorem cell23_4066276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_4066276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066276 prefixEnd_4066276 := by exact prefixLift 4066276
  have htrace : WordTrace (prefixWord ++ tailWord_4066276) baseStart_4066276 baseEnd_4066276 := by
    simpa [prefixWord, tailWord_4066276, baseEnd_4066276] using wordTrace_append hprefix tailTrace_4066276
  have hstable : (prefixWord ++ tailWord_4066276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066276).length < 2 ^ (prefixWord ++ tailWord_4066276).sum := by decide
  have hdescent : baseEnd_4066276 < baseStart_4066276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066316 : List Nat := [2, 2, 1, 2, 3, 4, 1, 8]
def baseStart_4066316 : Nat := 118140960795 + 4066316 * 2 ^ 59
def prefixEnd_4066316 : Nat := 4983230072969 + 3 ^ 40 * 4066316 * 2
def baseEnd_4066316 : Nat := 77332392632148805690717

theorem tailTrace_4066316 : CollatzResearch.WordTrace tailWord_4066316 prefixEnd_4066316 77332392632148805690717 := by
  unfold tailWord_4066316
  simp only [CollatzResearch.WordTrace]
  refine ⟨74155364368219539164105401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98873819157626052218807201 74155364368219539164105401)
  ·
    refine ⟨55616523276164654373079051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74155364368219539164105401 55616523276164654373079051)
    ·
      refine ⟨83424784914246981559618577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55616523276164654373079051 83424784914246981559618577)
      ·
        refine ⟨62568588685685236169713933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83424784914246981559618577 62568588685685236169713933)
        ·
          refine ⟨23463220757131963563642725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62568588685685236169713933 23463220757131963563642725)
          ·
            refine ⟨4399353891962243168183011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23463220757131963563642725 4399353891962243168183011)
            ·
              refine ⟨6599030837943364752274517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4399353891962243168183011 6599030837943364752274517)
              ·
                refine ⟨77332392632148805690717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6599030837943364752274517 77332392632148805690717)
                ·
                  rfl

theorem cell23_4066316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 8].length) (baseStart_4066316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066316 prefixEnd_4066316 := by exact prefixLift 4066316
  have htrace : WordTrace (prefixWord ++ tailWord_4066316) baseStart_4066316 baseEnd_4066316 := by
    simpa [prefixWord, tailWord_4066316, baseEnd_4066316] using wordTrace_append hprefix tailTrace_4066316
  have hstable : (prefixWord ++ tailWord_4066316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066316).length < 2 ^ (prefixWord ++ tailWord_4066316).sum := by decide
  have hdescent : baseEnd_4066316 < baseStart_4066316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066333 : List Nat := [1, 4, 2, 2, 3, 1, 3, 7]
def baseStart_4066333 : Nat := 118140960795 + 4066333 * 2 ^ 59
def prefixEnd_4066333 : Nat := 4983230072969 + 3 ^ 40 * 4066333 * 2
def baseEnd_4066333 : Nat := 77332715934783118042103

theorem tailTrace_4066333 : CollatzResearch.WordTrace tailWord_4066333 prefixEnd_4066333 77332715934783118042103 := by
  unfold tailWord_4066333
  simp only [CollatzResearch.WordTrace]
  refine ⟨148311348777377490231579653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98874232518251660154386435 148311348777377490231579653)
  ·
    refine ⟨27808377895758279418421185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148311348777377490231579653 27808377895758279418421185)
    ·
      refine ⟨20856283421818709563815889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27808377895758279418421185 20856283421818709563815889)
      ·
        refine ⟨15642212566364032172861917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20856283421818709563815889 15642212566364032172861917)
        ·
          refine ⟨5865829712386512064823219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15642212566364032172861917 5865829712386512064823219)
          ·
            refine ⟨8798744568579768097234829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5865829712386512064823219 8798744568579768097234829)
            ·
              refine ⟨3299529213217413036463061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8798744568579768097234829 3299529213217413036463061)
              ·
                refine ⟨77332715934783118042103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3299529213217413036463061 77332715934783118042103)
                ·
                  rfl

theorem cell23_4066333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 7].length) (baseStart_4066333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066333 prefixEnd_4066333 := by exact prefixLift 4066333
  have htrace : WordTrace (prefixWord ++ tailWord_4066333) baseStart_4066333 baseEnd_4066333 := by
    simpa [prefixWord, tailWord_4066333, baseEnd_4066333] using wordTrace_append hprefix tailTrace_4066333
  have hstable : (prefixWord ++ tailWord_4066333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066333).length < 2 ^ (prefixWord ++ tailWord_4066333).sum := by decide
  have hdescent : baseEnd_4066333 < baseStart_4066333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066360 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 2, 1, 3]
def baseStart_4066360 : Nat := 118140960795 + 4066360 * 2 ^ 59
def prefixEnd_4066360 : Nat := 4983230072969 + 3 ^ 40 * 4066360 * 2
def baseEnd_4066360 : Nat := 2087997194216815581499157

theorem tailTrace_4066360 : CollatzResearch.WordTrace tailWord_4066360 prefixEnd_4066360 2087997194216815581499157 := by
  unfold tailWord_4066360
  simp only [CollatzResearch.WordTrace]
  refine ⟨74156166774139836921406267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98874889032186449228541689 74156166774139836921406267)
  ·
    refine ⟨111234250161209755382109401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74156166774139836921406267 111234250161209755382109401)
    ·
      refine ⟨83425687620907316536582051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111234250161209755382109401 83425687620907316536582051)
      ·
        refine ⟨125138531431360974804873077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83425687620907316536582051 125138531431360974804873077)
        ·
          refine ⟨11731737321690091387956851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125138531431360974804873077 11731737321690091387956851)
          ·
            refine ⟨17597605982535137081935277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11731737321690091387956851 17597605982535137081935277)
            ·
              refine ⟨6599102243450676405725729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17597605982535137081935277 6599102243450676405725729)
              ·
                refine ⟨4949326682588007304294297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6599102243450676405725729 4949326682588007304294297)
                ·
                  refine ⟨3711995011941005478220723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4949326682588007304294297 3711995011941005478220723)
                  ·
                    refine ⟨5567992517911508217331085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3711995011941005478220723 5567992517911508217331085)
                    ·
                      refine ⟨2087997194216815581499157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5567992517911508217331085 2087997194216815581499157)
                      ·
                        rfl

theorem cell23_4066360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_4066360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066360 prefixEnd_4066360 := by exact prefixLift 4066360
  have htrace : WordTrace (prefixWord ++ tailWord_4066360) baseStart_4066360 baseEnd_4066360 := by
    simpa [prefixWord, tailWord_4066360, baseEnd_4066360] using wordTrace_append hprefix tailTrace_4066360
  have hstable : (prefixWord ++ tailWord_4066360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066360).length < 2 ^ (prefixWord ++ tailWord_4066360).sum := by decide
  have hdescent : baseEnd_4066360 < baseStart_4066360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066383 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 8, 2, 2]
def baseStart_4066383 : Nat := 118140960795 + 4066383 * 2 ^ 59
def prefixEnd_4066383 : Nat := 4983230072969 + 3 ^ 40 * 4066383 * 2
def baseEnd_4066383 : Nat := 2088009004271868991511551

theorem tailTrace_4066383 : CollatzResearch.WordTrace tailWord_4066383 prefixEnd_4066383 2088009004271868991511551 := by
  unfold tailWord_4066383
  simp only [CollatzResearch.WordTrace]
  refine ⟨148313172427196348770899803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98875448284797565847266535 148313172427196348770899803)
  ·
    refine ⟨222469758640794523156349705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148313172427196348770899803 222469758640794523156349705)
    ·
      refine ⟨166852318980595892367262279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222469758640794523156349705 166852318980595892367262279)
      ·
        refine ⟨250278478470893838550893419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166852318980595892367262279 250278478470893838550893419)
        ·
          refine ⟨375417717706340757826340129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250278478470893838550893419 375417717706340757826340129)
          ·
            refine ⟨281563288279755568369755097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375417717706340757826340129 281563288279755568369755097)
            ·
              refine ⟨211172466209816676277316323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281563288279755568369755097 211172466209816676277316323)
              ·
                refine ⟨316758699314725014415974485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211172466209816676277316323 316758699314725014415974485)
                ·
                  refine ⟨3712016007594433762687201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 316758699314725014415974485 3712016007594433762687201)
                  ·
                    refine ⟨2784012005695825322015401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3712016007594433762687201 2784012005695825322015401)
                    ·
                      refine ⟨2088009004271868991511551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2784012005695825322015401 2088009004271868991511551)
                      ·
                        rfl

theorem cell23_4066383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 2, 2].length) (baseStart_4066383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066383 prefixEnd_4066383 := by exact prefixLift 4066383
  have htrace : WordTrace (prefixWord ++ tailWord_4066383) baseStart_4066383 baseEnd_4066383 := by
    simpa [prefixWord, tailWord_4066383, baseEnd_4066383] using wordTrace_append hprefix tailTrace_4066383
  have hstable : (prefixWord ++ tailWord_4066383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066383).length < 2 ^ (prefixWord ++ tailWord_4066383).sum := by decide
  have hdescent : baseEnd_4066383 < baseStart_4066383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066419 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 11]
def baseStart_4066419 : Nat := 118140960795 + 4066419 * 2 ^ 59
def prefixEnd_4066419 : Nat := 4983230072969 + 3 ^ 40 * 4066419 * 2
def baseEnd_4066419 : Nat := 696009163191810283553795

theorem tailTrace_4066419 : CollatzResearch.WordTrace tailWord_4066419 prefixEnd_4066419 696009163191810283553795 := by
  unfold tailWord_4066419
  simp only [CollatzResearch.WordTrace]
  refine ⟨148314485455065926919210311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98876323636710617946140207 148314485455065926919210311)
  ·
    refine ⟨222471728182598890378815467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148314485455065926919210311 222471728182598890378815467)
    ·
      refine ⟨333707592273898335568223201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222471728182598890378815467 333707592273898335568223201)
      ·
        refine ⟨250280694205423751676167401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333707592273898335568223201 250280694205423751676167401)
        ·
          refine ⟨187710520654067813757125551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250280694205423751676167401 187710520654067813757125551)
          ·
            refine ⟨281565780981101720635688327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187710520654067813757125551 281565780981101720635688327)
            ·
              refine ⟨422348671471652580953532491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281565780981101720635688327 422348671471652580953532491)
              ·
                refine ⟨633523007207478871430298737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422348671471652580953532491 633523007207478871430298737)
                ·
                  refine ⟨475142255405609153572724053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633523007207478871430298737 475142255405609153572724053)
                  ·
                    refine ⟨696009163191810283553795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 475142255405609153572724053 696009163191810283553795)
                    ·
                      rfl

theorem cell23_4066419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 11].length) (baseStart_4066419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066419 prefixEnd_4066419 := by exact prefixLift 4066419
  have htrace : WordTrace (prefixWord ++ tailWord_4066419) baseStart_4066419 baseEnd_4066419 := by
    simpa [prefixWord, tailWord_4066419, baseEnd_4066419] using wordTrace_append hprefix tailTrace_4066419
  have hstable : (prefixWord ++ tailWord_4066419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066419).length < 2 ^ (prefixWord ++ tailWord_4066419).sum := by decide
  have hdescent : baseEnd_4066419 < baseStart_4066419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066474 : List Nat := [3, 1, 5, 1, 1, 3, 2, 2, 5]
def baseStart_4066474 : Nat := 118140960795 + 4066474 * 2 ^ 59
def prefixEnd_4066474 : Nat := 4983230072969 + 3 ^ 40 * 4066474 * 2
def baseEnd_4066474 : Nat := 232006192334603126163737

theorem tailTrace_4066474 : CollatzResearch.WordTrace tailWord_4066474 prefixEnd_4066474 232006192334603126163737 := by
  unfold tailWord_4066474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37079122867466667828115619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98877660979911114208308317 37079122867466667828115619)
  ·
    refine ⟨55618684301200001742173429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37079122867466667828115619 55618684301200001742173429)
    ·
      refine ⟨5214251653237500163328759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55618684301200001742173429 5214251653237500163328759)
      ·
        refine ⟨7821377479856250244993139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5214251653237500163328759 7821377479856250244993139)
        ·
          refine ⟨11732066219784375367489709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821377479856250244993139 11732066219784375367489709)
          ·
            refine ⟨4399524832419140762808641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11732066219784375367489709 4399524832419140762808641)
            ·
              refine ⟨3299643624314355572106481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399524832419140762808641 3299643624314355572106481)
              ·
                refine ⟨2474732718235766679079861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3299643624314355572106481 2474732718235766679079861)
                ·
                  refine ⟨232006192334603126163737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2474732718235766679079861 232006192334603126163737)
                  ·
                    rfl

theorem cell23_4066474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_4066474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066474 prefixEnd_4066474 := by exact prefixLift 4066474
  have htrace : WordTrace (prefixWord ++ tailWord_4066474) baseStart_4066474 baseEnd_4066474 := by
    simpa [prefixWord, tailWord_4066474, baseEnd_4066474] using wordTrace_append hprefix tailTrace_4066474
  have hstable : (prefixWord ++ tailWord_4066474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066474).length < 2 ^ (prefixWord ++ tailWord_4066474).sum := by decide
  have hdescent : baseEnd_4066474 < baseStart_4066474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066493 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_4066493 : Nat := 118140960795 + 4066493 * 2 ^ 59
def prefixEnd_4066493 : Nat := 4983230072969 + 3 ^ 40 * 4066493 * 2
def baseEnd_4066493 : Nat := 2088065487143863561136045

theorem tailTrace_4066493 : CollatzResearch.WordTrace tailWord_4066493 prefixEnd_4066493 2088065487143863561136045 := by
  unfold tailWord_4066493
  simp only [CollatzResearch.WordTrace]
  refine ⟨148317184456797837557404133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98878122971198558371602755 148317184456797837557404133)
  ·
    refine ⟨27809472085649594542013275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148317184456797837557404133 27809472085649594542013275)
    ·
      refine ⟨41714208128474391813019913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27809472085649594542013275 41714208128474391813019913)
      ·
        refine ⟨31285656096355793859764935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41714208128474391813019913 31285656096355793859764935)
        ·
          refine ⟨46928484144533690789647403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31285656096355793859764935 46928484144533690789647403)
          ·
            refine ⟨70392726216800536184471105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46928484144533690789647403 70392726216800536184471105)
            ·
              refine ⟨52794544662600402138353329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70392726216800536184471105 52794544662600402138353329)
              ·
                refine ⟨39595908496950301603764997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52794544662600402138353329 39595908496950301603764997)
                ·
                  refine ⟨7424232843178181550705937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39595908496950301603764997 7424232843178181550705937)
                  ·
                    refine ⟨5568174632383636163029453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7424232843178181550705937 5568174632383636163029453)
                    ·
                      refine ⟨2088065487143863561136045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568174632383636163029453 2088065487143863561136045)
                      ·
                        rfl

theorem cell23_4066493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_4066493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066493 prefixEnd_4066493 := by exact prefixLift 4066493
  have htrace : WordTrace (prefixWord ++ tailWord_4066493) baseStart_4066493 baseEnd_4066493 := by
    simpa [prefixWord, tailWord_4066493, baseEnd_4066493] using wordTrace_append hprefix tailTrace_4066493
  have hstable : (prefixWord ++ tailWord_4066493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066493).length < 2 ^ (prefixWord ++ tailWord_4066493).sum := by decide
  have hdescent : baseEnd_4066493 < baseStart_4066493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066510 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_4066510 : Nat := 118140960795 + 4066510 * 2 ^ 59
def prefixEnd_4066510 : Nat := 4983230072969 + 3 ^ 40 * 4066510 * 2
def baseEnd_4066510 : Nat := 2088074216314989994623467

theorem tailTrace_4066510 : CollatzResearch.WordTrace tailWord_4066510 prefixEnd_4066510 2088074216314989994623467 := by
  unfold tailWord_4066510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18539725562217031182596623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98878536331824166307181989 18539725562217031182596623)
  ·
    refine ⟨27809588343325546773894935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18539725562217031182596623 27809588343325546773894935)
    ·
      refine ⟨41714382514988320160842403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27809588343325546773894935 41714382514988320160842403)
      ·
        refine ⟨62571573772482480241263605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41714382514988320160842403 62571573772482480241263605)
        ·
          refine ⟨5866085041170232522618463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62571573772482480241263605 5866085041170232522618463)
          ·
            refine ⟨8799127561755348783927695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866085041170232522618463 8799127561755348783927695)
            ·
              refine ⟨13198691342633023175891543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799127561755348783927695 13198691342633023175891543)
              ·
                refine ⟨19798037013949534763837315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13198691342633023175891543 19798037013949534763837315)
                ·
                  refine ⟨29697055520924302145755973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19798037013949534763837315 29697055520924302145755973)
                  ·
                    refine ⟨5568197910173306652329245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29697055520924302145755973 5568197910173306652329245)
                    ·
                      refine ⟨2088074216314989994623467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568197910173306652329245 2088074216314989994623467)
                      ·
                        rfl

theorem cell23_4066510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_4066510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066510 prefixEnd_4066510 := by exact prefixLift 4066510
  have htrace : WordTrace (prefixWord ++ tailWord_4066510) baseStart_4066510 baseEnd_4066510 := by
    simpa [prefixWord, tailWord_4066510, baseEnd_4066510] using wordTrace_append hprefix tailTrace_4066510
  have hstable : (prefixWord ++ tailWord_4066510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066510).length < 2 ^ (prefixWord ++ tailWord_4066510).sum := by decide
  have hdescent : baseEnd_4066510 < baseStart_4066510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066517 : List Nat := [1, 3, 2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_4066517 : Nat := 118140960795 + 4066517 * 2 ^ 59
def prefixEnd_4066517 : Nat := 4983230072969 + 3 ^ 40 * 4066517 * 2
def baseEnd_4066517 : Nat := 696025936893190489078645

theorem tailTrace_4066517 : CollatzResearch.WordTrace tailWord_4066517 prefixEnd_4066517 696025936893190489078645 := by
  unfold tailWord_4066517
  simp only [CollatzResearch.WordTrace]
  refine ⟨148318059808710889656277805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98878706539140593104185203 148318059808710889656277805)
  ·
    refine ⟨55619272428266583621104177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148318059808710889656277805 55619272428266583621104177)
    ·
      refine ⟨41714454321199937715828133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55619272428266583621104177 41714454321199937715828133)
      ·
        refine ⟨7821460185224988321717775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41714454321199937715828133 7821460185224988321717775)
        ·
          refine ⟨11732190277837482482576663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821460185224988321717775 11732190277837482482576663)
          ·
            refine ⟨17598285416756223723864995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11732190277837482482576663 17598285416756223723864995)
            ·
              refine ⟨26397428125134335585797493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17598285416756223723864995 26397428125134335585797493)
              ·
                refine ⟨2474758886731343961168515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26397428125134335585797493 2474758886731343961168515)
                ·
                  refine ⟨3712138330097015941752773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474758886731343961168515 3712138330097015941752773)
                  ·
                    refine ⟨696025936893190489078645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3712138330097015941752773 696025936893190489078645)
                    ·
                      rfl

theorem cell23_4066517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_4066517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066517 prefixEnd_4066517 := by exact prefixLift 4066517
  have htrace : WordTrace (prefixWord ++ tailWord_4066517) baseStart_4066517 baseEnd_4066517 := by
    simpa [prefixWord, tailWord_4066517, baseEnd_4066517] using wordTrace_append hprefix tailTrace_4066517
  have hstable : (prefixWord ++ tailWord_4066517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066517).length < 2 ^ (prefixWord ++ tailWord_4066517).sum := by decide
  have hdescent : baseEnd_4066517 < baseStart_4066517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066540 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 3]
def baseStart_4066540 : Nat := 118140960795 + 4066540 * 2 ^ 59
def prefixEnd_4066540 : Nat := 4983230072969 + 3 ^ 40 * 4066540 * 2
def baseEnd_4066540 : Nat := 2088089620734624877248329

theorem tailTrace_4066540 : CollatzResearch.WordTrace tailWord_4066540 prefixEnd_4066540 2088089620734624877248329 := by
  unfold tailWord_4066540
  simp only [CollatzResearch.WordTrace]
  refine ⟨74159449343813782292182537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98879265791751709722910049 74159449343813782292182537)
  ·
    refine ⟨55619587007860336719136903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74159449343813782292182537 55619587007860336719136903)
    ·
      refine ⟨83429380511790505078705355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55619587007860336719136903 83429380511790505078705355)
      ·
        refine ⟨125144070767685757618058033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83429380511790505078705355 125144070767685757618058033)
        ·
          refine ⟨93858053075764318213543525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125144070767685757618058033 93858053075764318213543525)
          ·
            refine ⟨17598384951705809665039411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93858053075764318213543525 17598384951705809665039411)
            ·
              refine ⟨26397577427558714497559117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17598384951705809665039411 26397577427558714497559117)
              ·
                refine ⟨9899091535334517936584669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26397577427558714497559117 9899091535334517936584669)
                ·
                  refine ⟨3712159325750444226219251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9899091535334517936584669 3712159325750444226219251)
                  ·
                    refine ⟨5568238988625666339328877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712159325750444226219251 5568238988625666339328877)
                    ·
                      refine ⟨2088089620734624877248329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568238988625666339328877 2088089620734624877248329)
                      ·
                        rfl

theorem cell23_4066540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_4066540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066540 prefixEnd_4066540 := by exact prefixLift 4066540
  have htrace : WordTrace (prefixWord ++ tailWord_4066540) baseStart_4066540 baseEnd_4066540 := by
    simpa [prefixWord, tailWord_4066540, baseEnd_4066540] using wordTrace_append hprefix tailTrace_4066540
  have hstable : (prefixWord ++ tailWord_4066540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066540).length < 2 ^ (prefixWord ++ tailWord_4066540).sum := by decide
  have hdescent : baseEnd_4066540 < baseStart_4066540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066574 : List Nat := [4, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3]
def baseStart_4066574 : Nat := 118140960795 + 4066574 * 2 ^ 59
def prefixEnd_4066574 : Nat := 4983230072969 + 3 ^ 40 * 4066574 * 2
def baseEnd_4066574 : Nat := 2088107079076877744223173

theorem tailTrace_4066574 : CollatzResearch.WordTrace tailWord_4066574 prefixEnd_4066574 2088107079076877744223173 := by
  unfold tailWord_4066574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18540017346188048548887847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98880092513002925594068517 18540017346188048548887847)
  ·
    refine ⟨27810026019282072823331771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18540017346188048548887847 27810026019282072823331771)
    ·
      refine ⟨41715039028923109234997657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27810026019282072823331771 41715039028923109234997657)
      ·
        refine ⟨31286279271692331926248243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41715039028923109234997657 31286279271692331926248243)
        ·
          refine ⟨46929418907538497889372365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31286279271692331926248243 46929418907538497889372365)
          ·
            refine ⟨17598532090326936708514637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46929418907538497889372365 17598532090326936708514637)
            ·
              refine ⟨6599449533872601265692989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17598532090326936708514637 6599449533872601265692989)
              ·
                refine ⟨2474793575202225474634871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6599449533872601265692989 2474793575202225474634871)
                ·
                  refine ⟨3712190362803338211952307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474793575202225474634871 3712190362803338211952307)
                  ·
                    refine ⟨5568285544205007317928461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712190362803338211952307 5568285544205007317928461)
                    ·
                      refine ⟨2088107079076877744223173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568285544205007317928461 2088107079076877744223173)
                      ·
                        rfl

theorem cell23_4066574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_4066574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066574 prefixEnd_4066574 := by exact prefixLift 4066574
  have htrace : WordTrace (prefixWord ++ tailWord_4066574) baseStart_4066574 baseEnd_4066574 := by
    simpa [prefixWord, tailWord_4066574, baseEnd_4066574] using wordTrace_append hprefix tailTrace_4066574
  have hstable : (prefixWord ++ tailWord_4066574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066574).length < 2 ^ (prefixWord ++ tailWord_4066574).sum := by decide
  have hdescent : baseEnd_4066574 < baseStart_4066574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066591 : List Nat := [1, 1, 2, 4, 4, 1, 3, 2, 1, 1, 3]
def baseStart_4066591 : Nat := 118140960795 + 4066591 * 2 ^ 59
def prefixEnd_4066591 : Nat := 4983230072969 + 3 ^ 40 * 4066591 * 2
def baseEnd_4066591 : Nat := 2088115808248004177710595

theorem tailTrace_4066591 : CollatzResearch.WordTrace tailWord_4066591 prefixEnd_4066591 2088115808248004177710595 := by
  unfold tailWord_4066591
  simp only [CollatzResearch.WordTrace]
  refine ⟨148320758810442800294471627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98880505873628533529647751 148320758810442800294471627)
  ·
    refine ⟨222481138215664200441707441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148320758810442800294471627 222481138215664200441707441)
    ·
      refine ⟨166860853661748150331280581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222481138215664200441707441 166860853661748150331280581)
      ·
        refine ⟨31286410061577778187115109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166860853661748150331280581 31286410061577778187115109)
        ·
          refine ⟨5866201886545833410084083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31286410061577778187115109 5866201886545833410084083)
          ·
            refine ⟨8799302829818750115126125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866201886545833410084083 8799302829818750115126125)
            ·
              refine ⟨3299738561182031293172297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8799302829818750115126125 3299738561182031293172297)
              ·
                refine ⟨2474803920886523469879223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3299738561182031293172297 2474803920886523469879223)
                ·
                  refine ⟨3712205881329785204818835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2474803920886523469879223 3712205881329785204818835)
                  ·
                    refine ⟨5568308821994677807228253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712205881329785204818835 5568308821994677807228253)
                    ·
                      refine ⟨2088115808248004177710595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568308821994677807228253 2088115808248004177710595)
                      ·
                        rfl

theorem cell23_4066591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_4066591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066591 prefixEnd_4066591 := by exact prefixLift 4066591
  have htrace : WordTrace (prefixWord ++ tailWord_4066591) baseStart_4066591 baseEnd_4066591 := by
    simpa [prefixWord, tailWord_4066591, baseEnd_4066591] using wordTrace_append hprefix tailTrace_4066591
  have hstable : (prefixWord ++ tailWord_4066591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066591).length < 2 ^ (prefixWord ++ tailWord_4066591).sum := by decide
  have hdescent : baseEnd_4066591 < baseStart_4066591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066600 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4066600 : Nat := 118140960795 + 4066600 * 2 ^ 59
def prefixEnd_4066600 : Nat := 4983230072969 + 3 ^ 40 * 4066600 * 2
def baseEnd_4066600 : Nat := 2088120429573894642498053

theorem tailTrace_4066600 : CollatzResearch.WordTrace tailWord_4066600 prefixEnd_4066600 2088120429573894642498053 := by
  unfold tailWord_4066600
  simp only [CollatzResearch.WordTrace]
  refine ⟨74160543533705097415774627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98880724711606796554366169 74160543533705097415774627)
  ·
    refine ⟨111240815300557646123661941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74160543533705097415774627 111240815300557646123661941)
    ·
      refine ⟨10428826434427279324093307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111240815300557646123661941 10428826434427279324093307)
      ·
        refine ⟨15643239651640918986139961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10428826434427279324093307 15643239651640918986139961)
        ·
          refine ⟨11732429738730689239604971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15643239651640918986139961 11732429738730689239604971)
          ·
            refine ⟨17598644608096033859407457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11732429738730689239604971 17598644608096033859407457)
            ·
              refine ⟨13198983456072025394555593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17598644608096033859407457 13198983456072025394555593)
              ·
                refine ⟨9899237592054019045916695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13198983456072025394555593 9899237592054019045916695)
                ·
                  refine ⟨14848856388081028568875043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9899237592054019045916695 14848856388081028568875043)
                  ·
                    refine ⟨22273284582121542853312565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14848856388081028568875043 22273284582121542853312565)
                    ·
                      refine ⟨2088120429573894642498053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22273284582121542853312565 2088120429573894642498053)
                      ·
                        rfl

theorem cell23_4066600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4066600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066600 prefixEnd_4066600 := by exact prefixLift 4066600
  have htrace : WordTrace (prefixWord ++ tailWord_4066600) baseStart_4066600 baseEnd_4066600 := by
    simpa [prefixWord, tailWord_4066600, baseEnd_4066600] using wordTrace_append hprefix tailTrace_4066600
  have hstable : (prefixWord ++ tailWord_4066600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066600).length < 2 ^ (prefixWord ++ tailWord_4066600).sum := by decide
  have hdescent : baseEnd_4066600 < baseStart_4066600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066614 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4066614 : Nat := 118140960795 + 4066614 * 2 ^ 59
def prefixEnd_4066614 : Nat := 4983230072969 + 3 ^ 40 * 4066614 * 2
def baseEnd_4066614 : Nat := 2088127618303057587722989

theorem tailTrace_4066614 : CollatzResearch.WordTrace tailWord_4066614 prefixEnd_4066614 2088127618303057587722989 := by
  unfold tailWord_4066614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270099855584967201409931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98881065126239650148372597 9270099855584967201409931)
  ·
    refine ⟨13905149783377450802114897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9270099855584967201409931 13905149783377450802114897)
    ·
      refine ⟨10428862337533088101586173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13905149783377450802114897 10428862337533088101586173)
      ·
        refine ⟨3910823376574908038094815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10428862337533088101586173 3910823376574908038094815)
        ·
          refine ⟨5866235064862362057142223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910823376574908038094815 5866235064862362057142223)
          ·
            refine ⟨8799352597293543085713335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866235064862362057142223 8799352597293543085713335)
            ·
              refine ⟨13199028895940314628570003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799352597293543085713335 13199028895940314628570003)
              ·
                refine ⟨19798543343910471942855005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13199028895940314628570003 19798543343910471942855005)
                ·
                  refine ⟨7424453753966426978570627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19798543343910471942855005 7424453753966426978570627)
                  ·
                    refine ⟨11136680630949640467855941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7424453753966426978570627 11136680630949640467855941)
                    ·
                      refine ⟨2088127618303057587722989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11136680630949640467855941 2088127618303057587722989)
                      ·
                        rfl

theorem cell23_4066614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4066614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066614 prefixEnd_4066614 := by exact prefixLift 4066614
  have htrace : WordTrace (prefixWord ++ tailWord_4066614) baseStart_4066614 baseEnd_4066614 := by
    simpa [prefixWord, tailWord_4066614, baseEnd_4066614] using wordTrace_append hprefix tailTrace_4066614
  have hstable : (prefixWord ++ tailWord_4066614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066614).length < 2 ^ (prefixWord ++ tailWord_4066614).sum := by decide
  have hdescent : baseEnd_4066614 < baseStart_4066614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066617 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4066617 : Nat := 118140960795 + 4066617 * 2 ^ 59
def prefixEnd_4066617 : Nat := 4983230072969 + 3 ^ 40 * 4066617 * 2
def baseEnd_4066617 : Nat := 2088129158745021075985475

theorem tailTrace_4066617 : CollatzResearch.WordTrace tailWord_4066617 prefixEnd_4066617 2088129158745021075985475 := by
  unfold tailWord_4066617
  simp only [CollatzResearch.WordTrace]
  refine ⟨148321707108348606734918105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98881138072232404489945403 148321707108348606734918105)
  ·
    refine ⟨111241280331261455051188579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148321707108348606734918105 111241280331261455051188579)
    ·
      refine ⟨166861920496892182576782869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111241280331261455051188579 166861920496892182576782869)
      ·
        refine ⟨7821652523291821058286697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166861920496892182576782869 7821652523291821058286697)
        ·
          refine ⟨5866239392468865793715023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7821652523291821058286697 5866239392468865793715023)
          ·
            refine ⟨8799359088703298690572535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866239392468865793715023 8799359088703298690572535)
            ·
              refine ⟨13199038633054948035858803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8799359088703298690572535 13199038633054948035858803)
              ·
                refine ⟨19798557949582422053788205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13199038633054948035858803 19798557949582422053788205)
                ·
                  refine ⟨7424459231093408270170577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19798557949582422053788205 7424459231093408270170577)
                  ·
                    refine ⟨5568344423320056202627933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7424459231093408270170577 5568344423320056202627933)
                    ·
                      refine ⟨2088129158745021075985475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568344423320056202627933 2088129158745021075985475)
                      ·
                        rfl

theorem cell23_4066617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4066617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066617 prefixEnd_4066617 := by exact prefixLift 4066617
  have htrace : WordTrace (prefixWord ++ tailWord_4066617) baseStart_4066617 baseEnd_4066617 := by
    simpa [prefixWord, tailWord_4066617, baseEnd_4066617] using wordTrace_append hprefix tailTrace_4066617
  have hstable : (prefixWord ++ tailWord_4066617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066617).length < 2 ^ (prefixWord ++ tailWord_4066617).sum := by decide
  have hdescent : baseEnd_4066617 < baseStart_4066617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066637 : List Nat := [1, 6, 1, 3, 2, 10]
def baseStart_4066637 : Nat := 118140960795 + 4066637 * 2 ^ 59
def prefixEnd_4066637 : Nat := 4983230072969 + 3 ^ 40 * 4066637 * 2
def baseEnd_4066637 : Nat := 8593166371844078179981

theorem tailTrace_4066637 : CollatzResearch.WordTrace tailWord_4066637 prefixEnd_4066637 8593166371844078179981 := by
  unfold tailWord_4066637
  simp only [CollatzResearch.WordTrace]
  refine ⟨148322436568276150150646165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98881624378850766767097443 148322436568276150150646165)
  ·
    refine ⟨6952614214137944538311539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148322436568276150150646165 6952614214137944538311539)
    ·
      refine ⟨10428921321206916807467309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6952614214137944538311539 10428921321206916807467309)
      ·
        refine ⟨3910845495452593802800241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10428921321206916807467309 3910845495452593802800241)
        ·
          refine ⟨2933134121589445352100181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3910845495452593802800241 2933134121589445352100181)
          ·
            refine ⟨8593166371844078179981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2933134121589445352100181 8593166371844078179981)
            ·
              rfl

theorem cell23_4066637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 10].length) (baseStart_4066637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066637 prefixEnd_4066637 := by exact prefixLift 4066637
  have htrace : WordTrace (prefixWord ++ tailWord_4066637) baseStart_4066637 baseEnd_4066637 := by
    simpa [prefixWord, tailWord_4066637, baseEnd_4066637] using wordTrace_append hprefix tailTrace_4066637
  have hstable : (prefixWord ++ tailWord_4066637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066637).length < 2 ^ (prefixWord ++ tailWord_4066637).sum := by decide
  have hdescent : baseEnd_4066637 < baseStart_4066637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066647 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 3]
def baseStart_4066647 : Nat := 118140960795 + 4066647 * 2 ^ 59
def prefixEnd_4066647 : Nat := 4983230072969 + 3 ^ 40 * 4066647 * 2
def baseEnd_4066647 : Nat := 2088144563164655958610337

theorem tailTrace_4066647 : CollatzResearch.WordTrace tailWord_4066647 prefixEnd_4066647 2088144563164655958610337 := by
  unfold tailWord_4066647
  simp only [CollatzResearch.WordTrace]
  refine ⟨148322801298239921858510195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98881867532159947905673463 148322801298239921858510195)
  ·
    refine ⟨222484201947359882787765293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148322801298239921858510195 222484201947359882787765293)
    ·
      refine ⟨83431575730259956045411985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222484201947359882787765293 83431575730259956045411985)
      ·
        refine ⟨62573681797694967034058989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83431575730259956045411985 62573681797694967034058989)
        ·
          refine ⟨23465130674135612637772121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62573681797694967034058989 23465130674135612637772121)
          ·
            refine ⟨17598848005601709478329091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23465130674135612637772121 17598848005601709478329091)
            ·
              refine ⟨26398272008402564217493637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17598848005601709478329091 26398272008402564217493637)
              ·
                refine ⟨4949676001575480790780057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26398272008402564217493637 4949676001575480790780057)
                ·
                  refine ⟨3712257001181610593085043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4949676001575480790780057 3712257001181610593085043)
                  ·
                    refine ⟨5568385501772415889627565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712257001181610593085043 5568385501772415889627565)
                    ·
                      refine ⟨2088144563164655958610337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568385501772415889627565 2088144563164655958610337)
                      ·
                        rfl

theorem cell23_4066647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_4066647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066647 prefixEnd_4066647 := by exact prefixLift 4066647
  have htrace : WordTrace (prefixWord ++ tailWord_4066647) baseStart_4066647 baseEnd_4066647 := by
    simpa [prefixWord, tailWord_4066647, baseEnd_4066647] using wordTrace_append hprefix tailTrace_4066647
  have hstable : (prefixWord ++ tailWord_4066647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066647).length < 2 ^ (prefixWord ++ tailWord_4066647).sum := by decide
  have hdescent : baseEnd_4066647 < baseStart_4066647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066673 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_4066673 : Nat := 118140960795 + 4066673 * 2 ^ 59
def prefixEnd_4066673 : Nat := 4983230072969 + 3 ^ 40 * 4066673 * 2
def baseEnd_4066673 : Nat := 2088157913661672856885217

theorem tailTrace_4066673 : CollatzResearch.WordTrace tailWord_4066673 prefixEnd_4066673 2088157913661672856885217 := by
  unfold tailWord_4066673
  simp only [CollatzResearch.WordTrace]
  refine ⟨148323749596145728298956673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98882499730763818865971115 148323749596145728298956673)
  ·
    refine ⟨111242812197109296224217505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148323749596145728298956673 111242812197109296224217505)
    ·
      refine ⟨83432109147831972168163129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111242812197109296224217505 83432109147831972168163129)
      ·
        refine ⟨62574081860873979126122347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83432109147831972168163129 62574081860873979126122347)
        ·
          refine ⟨93861122791310968689183521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62574081860873979126122347 93861122791310968689183521)
          ·
            refine ⟨70395842093483226516887641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93861122791310968689183521 70395842093483226516887641)
            ·
              refine ⟨52796881570112419887665731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70395842093483226516887641 52796881570112419887665731)
              ·
                refine ⟨79195322355168629831498597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52796881570112419887665731 79195322355168629831498597)
                ·
                  refine ⟨14849122941594118093405987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79195322355168629831498597 14849122941594118093405987)
                  ·
                    refine ⟨22273684412391177140108981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14849122941594118093405987 22273684412391177140108981)
                    ·
                      refine ⟨2088157913661672856885217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22273684412391177140108981 2088157913661672856885217)
                      ·
                        rfl

theorem cell23_4066673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_4066673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066673 prefixEnd_4066673 := by exact prefixLift 4066673
  have htrace : WordTrace (prefixWord ++ tailWord_4066673) baseStart_4066673 baseEnd_4066673 := by
    simpa [prefixWord, tailWord_4066673, baseEnd_4066673] using wordTrace_append hprefix tailTrace_4066673
  have hstable : (prefixWord ++ tailWord_4066673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066673).length < 2 ^ (prefixWord ++ tailWord_4066673).sum := by decide
  have hdescent : baseEnd_4066673 < baseStart_4066673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066683 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 4]
def baseStart_4066683 : Nat := 118140960795 + 4066683 * 2 ^ 59
def prefixEnd_4066683 : Nat := 4983230072969 + 3 ^ 40 * 4066683 * 2
def baseEnd_4066683 : Nat := 2088163048468217817760171

theorem tailTrace_4066683 : CollatzResearch.WordTrace tailWord_4066683 prefixEnd_4066683 2088163048468217817760171 := by
  unfold tailWord_4066683
  simp only [CollatzResearch.WordTrace]
  refine ⟨148324114326109500006820703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98882742884073000004547135 148324114326109500006820703)
  ·
    refine ⟨222486171489164250010231055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148324114326109500006820703 222486171489164250010231055)
    ·
      refine ⟨333729257233746375015346583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222486171489164250010231055 333729257233746375015346583)
      ·
        refine ⟨500593885850619562523019875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333729257233746375015346583 500593885850619562523019875)
        ·
          refine ⟨750890828775929343784529813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500593885850619562523019875 750890828775929343784529813)
          ·
            refine ⟨35198007598871687989899835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 750890828775929343784529813 35198007598871687989899835)
            ·
              refine ⟨52797011398307531984849753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35198007598871687989899835 52797011398307531984849753)
              ·
                refine ⟨39597758548730648988637315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52797011398307531984849753 39597758548730648988637315)
                ·
                  refine ⟨59396637823095973482955973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39597758548730648988637315 59396637823095973482955973)
                  ·
                    refine ⟨11136869591830495028054245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59396637823095973482955973 11136869591830495028054245)
                    ·
                      refine ⟨2088163048468217817760171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11136869591830495028054245 2088163048468217817760171)
                      ·
                        rfl

theorem cell23_4066683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 4].length) (baseStart_4066683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066683 prefixEnd_4066683 := by exact prefixLift 4066683
  have htrace : WordTrace (prefixWord ++ tailWord_4066683) baseStart_4066683 baseEnd_4066683 := by
    simpa [prefixWord, tailWord_4066683, baseEnd_4066683] using wordTrace_append hprefix tailTrace_4066683
  have hstable : (prefixWord ++ tailWord_4066683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066683).length < 2 ^ (prefixWord ++ tailWord_4066683).sum := by decide
  have hdescent : baseEnd_4066683 < baseStart_4066683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066691 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 1, 3, 2]
def baseStart_4066691 : Nat := 118140960795 + 4066691 * 2 ^ 59
def prefixEnd_4066691 : Nat := 4983230072969 + 3 ^ 40 * 4066691 * 2
def baseEnd_4066691 : Nat := 2088167156313453786460135

theorem tailTrace_4066691 : CollatzResearch.WordTrace tailWord_4066691 prefixEnd_4066691 2088167156313453786460135 := by
  unfold tailWord_4066691
  simp only [CollatzResearch.WordTrace]
  refine ⟨148324406110080517373111927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98882937406720344915407951 148324406110080517373111927)
  ·
    refine ⟨222486609165120776059667891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148324406110080517373111927 222486609165120776059667891)
    ·
      refine ⟨333729913747681164089501837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222486609165120776059667891 333729913747681164089501837)
      ·
        refine ⟨125148717655380436533563189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333729913747681164089501837 125148717655380436533563189)
        ·
          refine ⟨11732692280191915925021549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125148717655380436533563189 11732692280191915925021549)
          ·
            refine ⟨4399759605071968471883081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11732692280191915925021549 4399759605071968471883081)
            ·
              refine ⟨3299819703803976353912311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399759605071968471883081 3299819703803976353912311)
              ·
                refine ⟨4949729555705964530868467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3299819703803976353912311 4949729555705964530868467)
                ·
                  refine ⟨7424594333558946796302701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4949729555705964530868467 7424594333558946796302701)
                  ·
                    refine ⟨2784222875084605048613513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7424594333558946796302701 2784222875084605048613513)
                    ·
                      refine ⟨2088167156313453786460135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2784222875084605048613513 2088167156313453786460135)
                      ·
                        rfl

theorem cell23_4066691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 3, 2].length) (baseStart_4066691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066691 prefixEnd_4066691 := by exact prefixLift 4066691
  have htrace : WordTrace (prefixWord ++ tailWord_4066691) baseStart_4066691 baseEnd_4066691 := by
    simpa [prefixWord, tailWord_4066691, baseEnd_4066691] using wordTrace_append hprefix tailTrace_4066691
  have hstable : (prefixWord ++ tailWord_4066691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066691).length < 2 ^ (prefixWord ++ tailWord_4066691).sum := by decide
  have hdescent : baseEnd_4066691 < baseStart_4066691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066720 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 3]
def baseStart_4066720 : Nat := 118140960795 + 4066720 * 2 ^ 59
def prefixEnd_4066720 : Nat := 4983230072969 + 3 ^ 40 * 4066720 * 2
def baseEnd_4066720 : Nat := 2088182047252434172997501

theorem tailTrace_4066720 : CollatzResearch.WordTrace tailWord_4066720 prefixEnd_4066720 2088182047252434172997501 := by
  unfold tailWord_4066720
  simp only [CollatzResearch.WordTrace]
  refine ⟨74162731913487727662958807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98883642551316970217278409 74162731913487727662958807)
  ·
    refine ⟨111244097870231591494438211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74162731913487727662958807 111244097870231591494438211)
    ·
      refine ⟨166866146805347387241657317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111244097870231591494438211 166866146805347387241657317)
      ·
        refine ⟨31287402526002635107810747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166866146805347387241657317 31287402526002635107810747)
        ·
          refine ⟨46931103789003952661716121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31287402526002635107810747 46931103789003952661716121)
          ·
            refine ⟨35198327841752964496287091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46931103789003952661716121 35198327841752964496287091)
            ·
              refine ⟨52797491762629446744430637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35198327841752964496287091 52797491762629446744430637)
              ·
                refine ⟨19799059410986042529161489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52797491762629446744430637 19799059410986042529161489)
                ·
                  refine ⟨14849294558239531896871117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19799059410986042529161489 14849294558239531896871117)
                  ·
                    refine ⟨5568485459339824461326669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14849294558239531896871117 5568485459339824461326669)
                    ·
                      refine ⟨2088182047252434172997501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568485459339824461326669 2088182047252434172997501)
                      ·
                        rfl

theorem cell23_4066720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_4066720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066720 prefixEnd_4066720 := by exact prefixLift 4066720
  have htrace : WordTrace (prefixWord ++ tailWord_4066720) baseStart_4066720 baseEnd_4066720 := by
    simpa [prefixWord, tailWord_4066720, baseEnd_4066720] using wordTrace_append hprefix tailTrace_4066720
  have hstable : (prefixWord ++ tailWord_4066720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066720).length < 2 ^ (prefixWord ++ tailWord_4066720).sum := by decide
  have hdescent : baseEnd_4066720 < baseStart_4066720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066723 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 3, 7]
def baseStart_4066723 : Nat := 118140960795 + 4066723 * 2 ^ 59
def prefixEnd_4066723 : Nat := 4983230072969 + 3 ^ 40 * 4066723 * 2
def baseEnd_4066723 : Nat := 696061195898132553753329

theorem tailTrace_4066723 : CollatzResearch.WordTrace tailWord_4066723 prefixEnd_4066723 696061195898132553753329 := by
  unfold tailWord_4066723
  simp only [CollatzResearch.WordTrace]
  refine ⟨148325573245964586838276823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98883715497309724558851215 148325573245964586838276823)
  ·
    refine ⟨222488359868946880257415235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148325573245964586838276823 222488359868946880257415235)
    ·
      refine ⟨333732539803420320386122853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222488359868946880257415235 333732539803420320386122853)
      ·
        refine ⟨62574851213141310072398035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333732539803420320386122853 62574851213141310072398035)
        ·
          refine ⟨93862276819711965108597053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62574851213141310072398035 93862276819711965108597053)
          ·
            refine ⟨35198353807391986915723895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93862276819711965108597053 35198353807391986915723895)
            ·
              refine ⟨52797530711087980373585843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35198353807391986915723895 52797530711087980373585843)
              ·
                refine ⟨79196296066631970560378765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52797530711087980373585843 79196296066631970560378765)
                ·
                  refine ⟨29698611024986988960142037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79196296066631970560378765 29698611024986988960142037)
                  ·
                    refine ⟨696061195898132553753329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29698611024986988960142037 696061195898132553753329)
                    ·
                      rfl

theorem cell23_4066723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 7].length) (baseStart_4066723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066723 prefixEnd_4066723 := by exact prefixLift 4066723
  have htrace : WordTrace (prefixWord ++ tailWord_4066723) baseStart_4066723 baseEnd_4066723 := by
    simpa [prefixWord, tailWord_4066723, baseEnd_4066723] using wordTrace_append hprefix tailTrace_4066723
  have hstable : (prefixWord ++ tailWord_4066723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066723).length < 2 ^ (prefixWord ++ tailWord_4066723).sum := by decide
  have hdescent : baseEnd_4066723 < baseStart_4066723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066750 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_4066750 : Nat := 118140960795 + 4066750 * 2 ^ 59
def prefixEnd_4066750 : Nat := 4983230072969 + 3 ^ 40 * 4066750 * 2
def baseEnd_4066750 : Nat := 2088197451672069055622363

theorem tailTrace_4066750 : CollatzResearch.WordTrace tailWord_4066750 prefixEnd_4066750 2088197451672069055622363 := by
  unfold tailWord_4066750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18540819752108346306188713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98884372011244513633006469 18540819752108346306188713)
  ·
    refine ⟨13905614814081259729641535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18540819752108346306188713 13905614814081259729641535)
    ·
      refine ⟨20858422221121889594462303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13905614814081259729641535 20858422221121889594462303)
      ·
        refine ⟨31287633331682834391693455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20858422221121889594462303 31287633331682834391693455)
        ·
          refine ⟨46931449997524251587540183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31287633331682834391693455 46931449997524251587540183)
          ·
            refine ⟨70397174996286377381310275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46931449997524251587540183 70397174996286377381310275)
            ·
              refine ⟨105595762494429566071965413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70397174996286377381310275 105595762494429566071965413)
              ·
                refine ⟨19799205467705543638493515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105595762494429566071965413 19799205467705543638493515)
                ·
                  refine ⟨29698808201558315457740273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19799205467705543638493515 29698808201558315457740273)
                  ·
                    refine ⟨22274106151168736593305205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29698808201558315457740273 22274106151168736593305205)
                    ·
                      refine ⟨2088197451672069055622363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22274106151168736593305205 2088197451672069055622363)
                      ·
                        rfl

theorem cell23_4066750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_4066750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066750 prefixEnd_4066750 := by exact prefixLift 4066750
  have htrace : WordTrace (prefixWord ++ tailWord_4066750) baseStart_4066750 baseEnd_4066750 := by
    simpa [prefixWord, tailWord_4066750, baseEnd_4066750] using wordTrace_append hprefix tailTrace_4066750
  have hstable : (prefixWord ++ tailWord_4066750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066750).length < 2 ^ (prefixWord ++ tailWord_4066750).sum := by decide
  have hdescent : baseEnd_4066750 < baseStart_4066750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066794 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_4066794 : Nat := 118140960795 + 4066794 * 2 ^ 59
def prefixEnd_4066794 : Nat := 4983230072969 + 3 ^ 40 * 4066794 * 2
def baseEnd_4066794 : Nat := 2088220044820866883472161

theorem tailTrace_4066794 : CollatzResearch.WordTrace tailWord_4066794 prefixEnd_4066794 2088220044820866883472161 := by
  unfold tailWord_4066794
  simp only [CollatzResearch.WordTrace]
  refine ⟨37082040707176841491027859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98885441885804910642740957 37082040707176841491027859)
  ·
    refine ⟨55623061060765262236541789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37082040707176841491027859 55623061060765262236541789)
    ·
      refine ⟨20858647897786973338703171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55623061060765262236541789 20858647897786973338703171)
      ·
        refine ⟨31287971846680460008054757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20858647897786973338703171 31287971846680460008054757)
        ·
          refine ⟨5866494721252586251510267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31287971846680460008054757 5866494721252586251510267)
          ·
            refine ⟨8799742081878879377265401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5866494721252586251510267 8799742081878879377265401)
            ·
              refine ⟨6599806561409159532949051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8799742081878879377265401 6599806561409159532949051)
              ·
                refine ⟨9899709842113739299423577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6599806561409159532949051 9899709842113739299423577)
                ·
                  refine ⟨7424782381585304474567683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9899709842113739299423577 7424782381585304474567683)
                  ·
                    refine ⟨11137173572377956711851525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7424782381585304474567683 11137173572377956711851525)
                    ·
                      refine ⟨2088220044820866883472161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11137173572377956711851525 2088220044820866883472161)
                      ·
                        rfl

theorem cell23_4066794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_4066794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066794 prefixEnd_4066794 := by exact prefixLift 4066794
  have htrace : WordTrace (prefixWord ++ tailWord_4066794) baseStart_4066794 baseEnd_4066794 := by
    simpa [prefixWord, tailWord_4066794, baseEnd_4066794] using wordTrace_append hprefix tailTrace_4066794
  have hstable : (prefixWord ++ tailWord_4066794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066794).length < 2 ^ (prefixWord ++ tailWord_4066794).sum := by decide
  have hdescent : baseEnd_4066794 < baseStart_4066794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066844 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_4066844 : Nat := 118140960795 + 4066844 * 2 ^ 59
def prefixEnd_4066844 : Nat := 4983230072969 + 3 ^ 40 * 4066844 * 2
def baseEnd_4066844 : Nat := 2088245718853591687846931

theorem tailTrace_4066844 : CollatzResearch.WordTrace tailWord_4066844 prefixEnd_4066844 2088245718853591687846931 := by
  unfold tailWord_4066844
  simp only [CollatzResearch.WordTrace]
  refine ⟨74164993239263112251715793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98886657652350816335621057 74164993239263112251715793)
  ·
    refine ⟨55623744929447334188786845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74164993239263112251715793 55623744929447334188786845)
    ·
      refine ⟨20858904348542750320795067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55623744929447334188786845 20858904348542750320795067)
      ·
        refine ⟨31288356522814125481192601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20858904348542750320795067 31288356522814125481192601)
        ·
          refine ⟨23466267392110594110894451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31288356522814125481192601 23466267392110594110894451)
          ·
            refine ⟨35199401088165891166341677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23466267392110594110894451 35199401088165891166341677)
            ·
              refine ⟨13199775408062209187378129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35199401088165891166341677 13199775408062209187378129)
              ·
                refine ⟨9899831556046656890533597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13199775408062209187378129 9899831556046656890533597)
                ·
                  refine ⟨3712436833517496333950099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9899831556046656890533597 3712436833517496333950099)
                  ·
                    refine ⟨5568655250276244500925149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712436833517496333950099 5568655250276244500925149)
                    ·
                      refine ⟨2088245718853591687846931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568655250276244500925149 2088245718853591687846931)
                      ·
                        rfl

theorem cell23_4066844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_4066844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066844 prefixEnd_4066844 := by exact prefixLift 4066844
  have htrace : WordTrace (prefixWord ++ tailWord_4066844) baseStart_4066844 baseEnd_4066844 := by
    simpa [prefixWord, tailWord_4066844, baseEnd_4066844] using wordTrace_append hprefix tailTrace_4066844
  have hstable : (prefixWord ++ tailWord_4066844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066844).length < 2 ^ (prefixWord ++ tailWord_4066844).sum := by decide
  have hdescent : baseEnd_4066844 < baseStart_4066844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066880 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_4066880 : Nat := 118140960795 + 4066880 * 2 ^ 59
def prefixEnd_4066880 : Nat := 4983230072969 + 3 ^ 40 * 4066880 * 2
def baseEnd_4066880 : Nat := 2088264204157153546996765

theorem tailTrace_4066880 : CollatzResearch.WordTrace tailWord_4066880 prefixEnd_4066880 2088264204157153546996765 := by
  unfold tailWord_4066880
  simp only [CollatzResearch.WordTrace]
  refine ⟨74165649753197901325871047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98887533004263868434494729 74165649753197901325871047)
  ·
    refine ⟨111248474629796851988806571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74165649753197901325871047 111248474629796851988806571)
    ·
      refine ⟨166872711944695277983209857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111248474629796851988806571 166872711944695277983209857)
      ·
        refine ⟨125154533958521458487407393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166872711944695277983209857 125154533958521458487407393)
        ·
          refine ⟨93865900468891093865555545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125154533958521458487407393 93865900468891093865555545)
          ·
            refine ⟨70399425351668320399166659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93865900468891093865555545 70399425351668320399166659)
            ·
              refine ⟨105599138027502480598749989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70399425351668320399166659 105599138027502480598749989)
              ·
                refine ⟨19799838380156715112265623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105599138027502480598749989 19799838380156715112265623)
                ·
                  refine ⟨29699757570235072668398435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19799838380156715112265623 29699757570235072668398435)
                  ·
                    refine ⟨44549636355352609002597653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29699757570235072668398435 44549636355352609002597653)
                    ·
                      refine ⟨2088264204157153546996765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44549636355352609002597653 2088264204157153546996765)
                      ·
                        rfl

theorem cell23_4066880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_4066880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066880 prefixEnd_4066880 := by exact prefixLift 4066880
  have htrace : WordTrace (prefixWord ++ tailWord_4066880) baseStart_4066880 baseEnd_4066880 := by
    simpa [prefixWord, tailWord_4066880, baseEnd_4066880] using wordTrace_append hprefix tailTrace_4066880
  have hstable : (prefixWord ++ tailWord_4066880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066880).length < 2 ^ (prefixWord ++ tailWord_4066880).sum := by decide
  have hdescent : baseEnd_4066880 < baseStart_4066880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066890 : List Nat := [3, 1, 2, 1, 1, 3, 2, 10]
def baseStart_4066890 : Nat := 118140960795 + 4066890 * 2 ^ 59
def prefixEnd_4066890 : Nat := 4983230072969 + 3 ^ 40 * 4066890 * 2
def baseEnd_4066890 : Nat := 77343308850507352143397

theorem tailTrace_4066890 : CollatzResearch.WordTrace tailWord_4066890 prefixEnd_4066890 77343308850507352143397 := by
  unfold tailWord_4066890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37082916059089893589901531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98887776157573049573070749 37082916059089893589901531)
  ·
    refine ⟨55624374088634840384852297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37082916059089893589901531 55624374088634840384852297)
    ·
      refine ⟨41718280566476130288639223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55624374088634840384852297 41718280566476130288639223)
      ·
        refine ⟨62577420849714195432958835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41718280566476130288639223 62577420849714195432958835)
        ·
          refine ⟨93866131274571293149438253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62577420849714195432958835 93866131274571293149438253)
          ·
            refine ⟨35199799227964234931039345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93866131274571293149438253 35199799227964234931039345)
            ·
              refine ⟨26399849420973176198279509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35199799227964234931039345 26399849420973176198279509)
              ·
                refine ⟨77343308850507352143397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26399849420973176198279509 77343308850507352143397)
                ·
                  rfl

theorem cell23_4066890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 10].length) (baseStart_4066890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066890 prefixEnd_4066890 := by exact prefixLift 4066890
  have htrace : WordTrace (prefixWord ++ tailWord_4066890) baseStart_4066890 baseEnd_4066890 := by
    simpa [prefixWord, tailWord_4066890, baseEnd_4066890] using wordTrace_append hprefix tailTrace_4066890
  have hstable : (prefixWord ++ tailWord_4066890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066890).length < 2 ^ (prefixWord ++ tailWord_4066890).sum := by decide
  have hdescent : baseEnd_4066890 < baseStart_4066890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066944 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 3, 3, 2]
def baseStart_4066944 : Nat := 118140960795 + 4066944 * 2 ^ 59
def prefixEnd_4066944 : Nat := 4983230072969 + 3 ^ 40 * 4066944 * 2
def baseEnd_4066944 : Nat := 2088297066919041296596471

theorem tailTrace_4066944 : CollatzResearch.WordTrace tailWord_4066944 prefixEnd_4066944 2088297066919041296596471 := by
  unfold tailWord_4066944
  simp only [CollatzResearch.WordTrace]
  refine ⟨74166816889081970791035943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98889089185442627721381257 74166816889081970791035943)
  ·
    refine ⟨111250225333622956186553915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74166816889081970791035943 111250225333622956186553915)
    ·
      refine ⟨166875338000434434279830873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111250225333622956186553915 166875338000434434279830873)
      ·
        refine ⟨125156503500325825709873155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166875338000434434279830873 125156503500325825709873155)
        ·
          refine ⟨187734755250488738564809733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125156503500325825709873155 187734755250488738564809733)
          ·
            refine ⟨35200266609466638480901825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187734755250488738564809733 35200266609466638480901825)
            ·
              refine ⟨26400199957099978860676369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35200266609466638480901825 26400199957099978860676369)
              ·
                refine ⟨19800149967824984145507277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26400199957099978860676369 19800149967824984145507277)
                ·
                  refine ⟨7425056237934369054565229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19800149967824984145507277 7425056237934369054565229)
                  ·
                    refine ⟨2784396089225388395461961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7425056237934369054565229 2784396089225388395461961)
                    ·
                      refine ⟨2088297066919041296596471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2784396089225388395461961 2088297066919041296596471)
                      ·
                        rfl

theorem cell23_4066944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_4066944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066944 prefixEnd_4066944 := by exact prefixLift 4066944
  have htrace : WordTrace (prefixWord ++ tailWord_4066944) baseStart_4066944 baseEnd_4066944 := by
    simpa [prefixWord, tailWord_4066944, baseEnd_4066944] using wordTrace_append hprefix tailTrace_4066944
  have hstable : (prefixWord ++ tailWord_4066944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066944).length < 2 ^ (prefixWord ++ tailWord_4066944).sum := by decide
  have hdescent : baseEnd_4066944 < baseStart_4066944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4066951 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_4066951 : Nat := 118140960795 + 4066951 * 2 ^ 59
def prefixEnd_4066951 : Nat := 4983230072969 + 3 ^ 40 * 4066951 * 2
def baseEnd_4066951 : Nat := 2088300661283622769208939

theorem tailTrace_4066951 : CollatzResearch.WordTrace tailWord_4066951 prefixEnd_4066951 2088300661283622769208939 := by
  unfold tailWord_4066951
  simp only [CollatzResearch.WordTrace]
  refine ⟨148333889089138581777576707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98889259392759054518384471 148333889089138581777576707)
  ·
    refine ⟨222500833633707872666365061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148333889089138581777576707 222500833633707872666365061)
    ·
      refine ⟨41718906306320226124943449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222500833633707872666365061 41718906306320226124943449)
      ·
        refine ⟨31289179729740169593707587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41718906306320226124943449 31289179729740169593707587)
        ·
          refine ⟨46933769594610254390561381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31289179729740169593707587 46933769594610254390561381)
          ·
            refine ⟨8800081798989422698230259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46933769594610254390561381 8800081798989422698230259)
            ·
              refine ⟨13200122698484134047345389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8800081798989422698230259 13200122698484134047345389)
              ·
                refine ⟨4950046011931550267754521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13200122698484134047345389 4950046011931550267754521)
                ·
                  refine ⟨3712534508948662700815891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4950046011931550267754521 3712534508948662700815891)
                  ·
                    refine ⟨5568801763422994051223837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712534508948662700815891 5568801763422994051223837)
                    ·
                      refine ⟨2088300661283622769208939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568801763422994051223837 2088300661283622769208939)
                      ·
                        rfl

theorem cell23_4066951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_4066951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4066951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4066951 prefixEnd_4066951 := by exact prefixLift 4066951
  have htrace : WordTrace (prefixWord ++ tailWord_4066951) baseStart_4066951 baseEnd_4066951 := by
    simpa [prefixWord, tailWord_4066951, baseEnd_4066951] using wordTrace_append hprefix tailTrace_4066951
  have hstable : (prefixWord ++ tailWord_4066951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4066951).length < 2 ^ (prefixWord ++ tailWord_4066951).sum := by decide
  have hdescent : baseEnd_4066951 < baseStart_4066951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4066951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067004 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_4067004 : Nat := 118140960795 + 4067004 * 2 ^ 59
def prefixEnd_4067004 : Nat := 4983230072969 + 3 ^ 40 * 4067004 * 2
def baseEnd_4067004 : Nat := 2088327875758311061846195

theorem tailTrace_4067004 : CollatzResearch.WordTrace tailWord_4067004 prefixEnd_4067004 2088327875758311061846195 := by
  unfold tailWord_4067004
  simp only [CollatzResearch.WordTrace]
  refine ⟨74167911078973285914628033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98890548105297714552837377 74167911078973285914628033)
  ·
    refine ⟨55625933309229964435971025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74167911078973285914628033 55625933309229964435971025)
    ·
      refine ⟨41719449981922473326978269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55625933309229964435971025 41719449981922473326978269)
      ·
        refine ⟨15644793743220927497616851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41719449981922473326978269 15644793743220927497616851)
        ·
          refine ⟨23467190614831391246425277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15644793743220927497616851 23467190614831391246425277)
          ·
            refine ⟨8800196480561771717409479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23467190614831391246425277 8800196480561771717409479)
            ·
              refine ⟨13200294720842657576114219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8800196480561771717409479 13200294720842657576114219)
              ·
                refine ⟨19800442081263986364171329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13200294720842657576114219 19800442081263986364171329)
                ·
                  refine ⟨14850331560947989773128497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19800442081263986364171329 14850331560947989773128497)
                  ·
                    refine ⟨11137748670710992329846373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14850331560947989773128497 11137748670710992329846373)
                    ·
                      refine ⟨2088327875758311061846195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11137748670710992329846373 2088327875758311061846195)
                      ·
                        rfl

theorem cell23_4067004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_4067004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067004 prefixEnd_4067004 := by exact prefixLift 4067004
  have htrace : WordTrace (prefixWord ++ tailWord_4067004) baseStart_4067004 baseEnd_4067004 := by
    simpa [prefixWord, tailWord_4067004, baseEnd_4067004] using wordTrace_append hprefix tailTrace_4067004
  have hstable : (prefixWord ++ tailWord_4067004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067004).length < 2 ^ (prefixWord ++ tailWord_4067004).sum := by decide
  have hdescent : baseEnd_4067004 < baseStart_4067004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067064 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 1, 6, 2]
def baseStart_4067064 : Nat := 118140960795 + 4067064 * 2 ^ 59
def prefixEnd_4067064 : Nat := 4983230072969 + 3 ^ 40 * 4067064 * 2
def baseEnd_4067064 : Nat := 2088358684597580827095919

theorem tailTrace_4067064 : CollatzResearch.WordTrace tailWord_4067064 prefixEnd_4067064 2088358684597580827095919 := by
  unfold tailWord_4067064
  simp only [CollatzResearch.WordTrace]
  refine ⟨74169005268864601038220123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98892007025152801384293497 74169005268864601038220123)
  ·
    refine ⟨111253507903296901557330185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74169005268864601038220123 111253507903296901557330185)
    ·
      refine ⟨83440130927472676167997639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111253507903296901557330185 83440130927472676167997639)
      ·
        refine ⟨125160196391209014251996459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83440130927472676167997639 125160196391209014251996459)
        ·
          refine ⟨187740294586813521377994689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125160196391209014251996459 187740294586813521377994689)
          ·
            refine ⟨140805220940110141033496017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187740294586813521377994689 140805220940110141033496017)
            ·
              refine ⟨105603915705082605775122013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140805220940110141033496017 105603915705082605775122013)
              ·
                refine ⟨39601468389405977165670755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105603915705082605775122013 39601468389405977165670755)
                ·
                  refine ⟨59402202584108965748506133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39601468389405977165670755 59402202584108965748506133)
                  ·
                    refine ⟨2784478246130107769461225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59402202584108965748506133 2784478246130107769461225)
                    ·
                      refine ⟨2088358684597580827095919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2784478246130107769461225 2088358684597580827095919)
                      ·
                        rfl

theorem cell23_4067064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_4067064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067064 prefixEnd_4067064 := by exact prefixLift 4067064
  have htrace : WordTrace (prefixWord ++ tailWord_4067064) baseStart_4067064 baseEnd_4067064 := by
    simpa [prefixWord, tailWord_4067064, baseEnd_4067064] using wordTrace_append hprefix tailTrace_4067064
  have hstable : (prefixWord ++ tailWord_4067064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067064).length < 2 ^ (prefixWord ++ tailWord_4067064).sum := by decide
  have hdescent : baseEnd_4067064 < baseStart_4067064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067074 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4067074 : Nat := 118140960795 + 4067074 * 2 ^ 59
def prefixEnd_4067074 : Nat := 4983230072969 + 3 ^ 40 * 4067074 * 2
def baseEnd_4067074 : Nat := 696121273134708595990291

theorem tailTrace_4067074 : CollatzResearch.WordTrace tailWord_4067074 prefixEnd_4067074 696121273134708595990291 := by
  unfold tailWord_4067074
  simp only [CollatzResearch.WordTrace]
  refine ⟨37084593816923243446076069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98892250178461982522869517 37084593816923243446076069)
  ·
    refine ⟨6953361340673108146139263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37084593816923243446076069 6953361340673108146139263)
    ·
      refine ⟨10430042011009662219208895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6953361340673108146139263 10430042011009662219208895)
      ·
        refine ⟨15645063016514493328813343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10430042011009662219208895 15645063016514493328813343)
        ·
          refine ⟨23467594524771739993220015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15645063016514493328813343 23467594524771739993220015)
          ·
            refine ⟨35201391787157609989830023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23467594524771739993220015 35201391787157609989830023)
            ·
              refine ⟨52802087680736414984745035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35201391787157609989830023 52802087680736414984745035)
              ·
                refine ⟨79203131521104622477117553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52802087680736414984745035 79203131521104622477117553)
                ·
                  refine ⟨59402348640828466857838165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79203131521104622477117553 59402348640828466857838165)
                  ·
                    refine ⟨696121273134708595990291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59402348640828466857838165 696121273134708595990291)
                    ·
                      rfl

theorem cell23_4067074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4067074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067074 prefixEnd_4067074 := by exact prefixLift 4067074
  have htrace : WordTrace (prefixWord ++ tailWord_4067074) baseStart_4067074 baseEnd_4067074 := by
    simpa [prefixWord, tailWord_4067074, baseEnd_4067074] using wordTrace_append hprefix tailTrace_4067074
  have hstable : (prefixWord ++ tailWord_4067074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067074).length < 2 ^ (prefixWord ++ tailWord_4067074).sum := by decide
  have hdescent : baseEnd_4067074 < baseStart_4067074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067084 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_4067084 : Nat := 118140960795 + 4067084 * 2 ^ 59
def prefixEnd_4067084 : Nat := 4983230072969 + 3 ^ 40 * 4067084 * 2
def baseEnd_4067084 : Nat := 2088368954210670748845827

theorem tailTrace_4067084 : CollatzResearch.WordTrace tailWord_4067084 prefixEnd_4067084 2088368954210670748845827 := by
  unfold tailWord_4067084
  simp only [CollatzResearch.WordTrace]
  refine ⟨74169369998828372746084153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98892493331771163661445537 74169369998828372746084153)
  ·
    refine ⟨55627027499121279559563115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74169369998828372746084153 55627027499121279559563115)
    ·
      refine ⟨83440541248681919339344673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55627027499121279559563115 83440541248681919339344673)
      ·
        refine ⟨62580405936511439504508505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83440541248681919339344673 62580405936511439504508505)
        ·
          refine ⟨46935304452383579628381379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62580405936511439504508505 46935304452383579628381379)
          ·
            refine ⟨70402956678575369442572069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46935304452383579628381379 70402956678575369442572069)
            ·
              refine ⟨13200554377232881770482263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70402956678575369442572069 13200554377232881770482263)
              ·
                refine ⟨19800831565849322655723395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13200554377232881770482263 19800831565849322655723395)
                ·
                  refine ⟨29701247348773983983585093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19800831565849322655723395 29701247348773983983585093)
                  ·
                    refine ⟨5568983877895121996922205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29701247348773983983585093 5568983877895121996922205)
                    ·
                      refine ⟨2088368954210670748845827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5568983877895121996922205 2088368954210670748845827)
                      ·
                        rfl

theorem cell23_4067084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_4067084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067084 prefixEnd_4067084 := by exact prefixLift 4067084
  have htrace : WordTrace (prefixWord ++ tailWord_4067084) baseStart_4067084 baseEnd_4067084 := by
    simpa [prefixWord, tailWord_4067084, baseEnd_4067084] using wordTrace_append hprefix tailTrace_4067084
  have hstable : (prefixWord ++ tailWord_4067084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067084).length < 2 ^ (prefixWord ++ tailWord_4067084).sum := by decide
  have hdescent : baseEnd_4067084 < baseStart_4067084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067091 : List Nat := [1, 1, 1, 2, 1, 3, 2, 7, 1, 4]
def baseStart_4067091 : Nat := 118140960795 + 4067091 * 2 ^ 59
def prefixEnd_4067091 : Nat := 4983230072969 + 3 ^ 40 * 4067091 * 2
def baseEnd_4067091 : Nat := 696124182858417407152765

theorem tailTrace_4067091 : CollatzResearch.WordTrace tailWord_4067091 prefixEnd_4067091 696124182858417407152765 := by
  unfold tailWord_4067091
  simp only [CollatzResearch.WordTrace]
  refine ⟨148338995308631385687673127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98892663539087590458448751 148338995308631385687673127)
  ·
    refine ⟨222508492962947078531509691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148338995308631385687673127 222508492962947078531509691)
    ·
      refine ⟨333762739444420617797264537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222508492962947078531509691 333762739444420617797264537)
      ·
        refine ⟨250322054583315463347948403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333762739444420617797264537 250322054583315463347948403)
        ·
          refine ⟨375483081874973195021922605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250322054583315463347948403 375483081874973195021922605)
          ·
            refine ⟨140806155703114948133220977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375483081874973195021922605 140806155703114948133220977)
            ·
              refine ⟨105604616777336211099915733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140806155703114948133220977 105604616777336211099915733)
              ·
                refine ⟨2475108205718817447654275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105604616777336211099915733 2475108205718817447654275)
                ·
                  refine ⟨3712662308578226171481413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475108205718817447654275 3712662308578226171481413)
                  ·
                    refine ⟨696124182858417407152765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3712662308578226171481413 696124182858417407152765)
                    ·
                      rfl

theorem cell23_4067091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 4].length) (baseStart_4067091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067091 prefixEnd_4067091 := by exact prefixLift 4067091
  have htrace : WordTrace (prefixWord ++ tailWord_4067091) baseStart_4067091 baseEnd_4067091 := by
    simpa [prefixWord, tailWord_4067091, baseEnd_4067091] using wordTrace_append hprefix tailTrace_4067091
  have hstable : (prefixWord ++ tailWord_4067091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067091).length < 2 ^ (prefixWord ++ tailWord_4067091).sum := by decide
  have hdescent : baseEnd_4067091 < baseStart_4067091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067104 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 6]
def baseStart_4067104 : Nat := 118140960795 + 4067104 * 2 ^ 59
def prefixEnd_4067104 : Nat := 4983230072969 + 3 ^ 40 * 4067104 * 2
def baseEnd_4067104 : Nat := 232042135980417852288415

theorem tailTrace_4067104 : CollatzResearch.WordTrace tailWord_4067104 prefixEnd_4067104 232042135980417852288415 := by
  unfold tailWord_4067104
  simp only [CollatzResearch.WordTrace]
  refine ⟨74169734728792144453948183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98892979638389525938597577 74169734728792144453948183)
  ·
    refine ⟨111254602093188216680922275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74169734728792144453948183 111254602093188216680922275)
    ·
      refine ⟨166881903139782325021383413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111254602093188216680922275 166881903139782325021383413)
      ·
        refine ⟨15645178419354592970754695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166881903139782325021383413 15645178419354592970754695)
        ·
          refine ⟨23467767629031889456132043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15645178419354592970754695 23467767629031889456132043)
          ·
            refine ⟨35201651443547834184198065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23467767629031889456132043 35201651443547834184198065)
            ·
              refine ⟨26401238582660875638148549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35201651443547834184198065 26401238582660875638148549)
              ·
                refine ⟨4950232234248914182152853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26401238582660875638148549 4950232234248914182152853)
                ·
                  refine ⟨232042135980417852288415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4950232234248914182152853 232042135980417852288415)
                  ·
                    rfl

theorem cell23_4067104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 6].length) (baseStart_4067104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067104 prefixEnd_4067104 := by exact prefixLift 4067104
  have htrace : WordTrace (prefixWord ++ tailWord_4067104) baseStart_4067104 baseEnd_4067104 := by
    simpa [prefixWord, tailWord_4067104, baseEnd_4067104] using wordTrace_append hprefix tailTrace_4067104
  have hstable : (prefixWord ++ tailWord_4067104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067104).length < 2 ^ (prefixWord ++ tailWord_4067104).sum := by decide
  have hdescent : baseEnd_4067104 < baseStart_4067104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067107 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 8]
def baseStart_4067107 : Nat := 118140960795 + 4067107 * 2 ^ 59
def prefixEnd_4067107 : Nat := 4983230072969 + 3 ^ 40 * 4067107 * 2
def baseEnd_4067107 : Nat := 2088380764265724158858221

theorem tailTrace_4067107 : CollatzResearch.WordTrace tailWord_4067107 prefixEnd_4067107 2088380764265724158858221 := by
  unfold tailWord_4067107
  simp only [CollatzResearch.WordTrace]
  refine ⟨148339578876573420420255575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98893052584382280280170383 148339578876573420420255575)
  ·
    refine ⟨222509368314860130630383363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148339578876573420420255575 222509368314860130630383363)
    ·
      refine ⟨333764052472290195945575045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222509368314860130630383363 333764052472290195945575045)
      ·
        refine ⟨62580759838554411739795321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333764052472290195945575045 62580759838554411739795321)
        ·
          refine ⟨46935569878915808804846491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62580759838554411739795321 46935569878915808804846491)
          ·
            refine ⟨70403354818373713207269737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46935569878915808804846491 70403354818373713207269737)
            ·
              refine ⟨52802516113780284905452303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70403354818373713207269737 52802516113780284905452303)
              ·
                refine ⟨79203774170670427358178455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52802516113780284905452303 79203774170670427358178455)
                ·
                  refine ⟨118805661256005641037267683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79203774170670427358178455 118805661256005641037267683)
                  ·
                    refine ⟨178208491884008461555901525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118805661256005641037267683 178208491884008461555901525)
                    ·
                      refine ⟨2088380764265724158858221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 178208491884008461555901525 2088380764265724158858221)
                      ·
                        rfl

theorem cell23_4067107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_4067107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067107 prefixEnd_4067107 := by exact prefixLift 4067107
  have htrace : WordTrace (prefixWord ++ tailWord_4067107) baseStart_4067107 baseEnd_4067107 := by
    simpa [prefixWord, tailWord_4067107, baseEnd_4067107] using wordTrace_append hprefix tailTrace_4067107
  have hstable : (prefixWord ++ tailWord_4067107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067107).length < 2 ^ (prefixWord ++ tailWord_4067107).sum := by decide
  have hdescent : baseEnd_4067107 < baseStart_4067107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067108 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_4067108 : Nat := 118140960795 + 4067108 * 2 ^ 59
def prefixEnd_4067108 : Nat := 4983230072969 + 3 ^ 40 * 4067108 * 2
def baseEnd_4067108 : Nat := 696127092582126218315239

theorem tailTrace_4067108 : CollatzResearch.WordTrace tailWord_4067108 prefixEnd_4067108 696127092582126218315239 := by
  unfold tailWord_4067108
  simp only [CollatzResearch.WordTrace]
  refine ⟨74169807674784898795520989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98893076899713198394027985 74169807674784898795520989)
  ·
    refine ⟨27813677878044337048320371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74169807674784898795520989 27813677878044337048320371)
    ·
      refine ⟨41720516817066505572480557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27813677878044337048320371 41720516817066505572480557)
      ·
        refine ⟨15645193806399939589680209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41720516817066505572480557 15645193806399939589680209)
        ·
          refine ⟨11733895354799954692260157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15645193806399939589680209 11733895354799954692260157)
          ·
            refine ⟨4400210758049983009597559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11733895354799954692260157 4400210758049983009597559)
            ·
              refine ⟨6600316137074974514396339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400210758049983009597559 6600316137074974514396339)
              ·
                refine ⟨9900474205612461771594509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6600316137074974514396339 9900474205612461771594509)
                ·
                  refine ⟨3712677827104673164347941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9900474205612461771594509 3712677827104673164347941)
                  ·
                    refine ⟨696127092582126218315239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3712677827104673164347941 696127092582126218315239)
                    ·
                      rfl

theorem cell23_4067108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_4067108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067108 prefixEnd_4067108 := by exact prefixLift 4067108
  have htrace : WordTrace (prefixWord ++ tailWord_4067108) baseStart_4067108 baseEnd_4067108 := by
    simpa [prefixWord, tailWord_4067108, baseEnd_4067108] using wordTrace_append hprefix tailTrace_4067108
  have hstable : (prefixWord ++ tailWord_4067108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067108).length < 2 ^ (prefixWord ++ tailWord_4067108).sum := by decide
  have hdescent : baseEnd_4067108 < baseStart_4067108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067121 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 6]
def baseStart_4067121 : Nat := 118140960795 + 4067121 * 2 ^ 59
def prefixEnd_4067121 : Nat := 4983230072969 + 3 ^ 40 * 4067121 * 2
def baseEnd_4067121 : Nat := 232043105888320789342573

theorem tailTrace_4067121 : CollatzResearch.WordTrace tailWord_4067121 prefixEnd_4067121 232043105888320789342573 := by
  unfold tailWord_4067121
  simp only [CollatzResearch.WordTrace]
  refine ⟨148340089498522700811265217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98893392999015133874176811 148340089498522700811265217)
  ·
    refine ⟨111255067123892025608448913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148340089498522700811265217 111255067123892025608448913)
    ·
      refine ⟨83441300342919019206336685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111255067123892025608448913 83441300342919019206336685)
      ·
        refine ⟨31290487628594632202376257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83441300342919019206336685 31290487628594632202376257)
        ·
          refine ⟨23467865721445974151782193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31290487628594632202376257 23467865721445974151782193)
          ·
            refine ⟨17600899291084480613836645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23467865721445974151782193 17600899291084480613836645)
            ·
              refine ⟨3300168617078340115094371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17600899291084480613836645 3300168617078340115094371)
              ·
                refine ⟨4950252925617510172641557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300168617078340115094371 4950252925617510172641557)
                ·
                  refine ⟨232043105888320789342573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4950252925617510172641557 232043105888320789342573)
                  ·
                    rfl

theorem cell23_4067121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 6].length) (baseStart_4067121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067121 prefixEnd_4067121 := by exact prefixLift 4067121
  have htrace : WordTrace (prefixWord ++ tailWord_4067121) baseStart_4067121 baseEnd_4067121 := by
    simpa [prefixWord, tailWord_4067121, baseEnd_4067121] using wordTrace_append hprefix tailTrace_4067121
  have hstable : (prefixWord ++ tailWord_4067121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067121).length < 2 ^ (prefixWord ++ tailWord_4067121).sum := by decide
  have hdescent : baseEnd_4067121 < baseStart_4067121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067127 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_4067127 : Nat := 118140960795 + 4067127 * 2 ^ 59
def prefixEnd_4067127 : Nat := 4983230072969 + 3 ^ 40 * 4067127 * 2
def baseEnd_4067127 : Nat := 2088391033878814080608129

theorem tailTrace_4067127 : CollatzResearch.WordTrace tailWord_4067127 prefixEnd_4067127 2088391033878814080608129 := by
  unfold tailWord_4067127
  simp only [CollatzResearch.WordTrace]
  refine ⟨148340308336500963835983635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98893538891000642557322423 148340308336500963835983635)
  ·
    refine ⟨222510462504751445753975453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148340308336500963835983635 222510462504751445753975453)
    ·
      refine ⟨83441423439281792157740795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222510462504751445753975453 83441423439281792157740795)
      ·
        refine ⟨125162135158922688236611193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83441423439281792157740795 125162135158922688236611193)
        ·
          refine ⟨93871601369192016177458395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125162135158922688236611193 93871601369192016177458395)
          ·
            refine ⟨140807402053788024266187593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93871601369192016177458395 140807402053788024266187593)
            ·
              refine ⟨105605551540341018199640695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140807402053788024266187593 105605551540341018199640695)
              ·
                refine ⟨158408327310511527299461043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105605551540341018199640695 158408327310511527299461043)
                ·
                  refine ⟨237612490965767290949191565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158408327310511527299461043 237612490965767290949191565)
                  ·
                    refine ⟨89104684112162734105946837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237612490965767290949191565 89104684112162734105946837)
                    ·
                      refine ⟨2088391033878814080608129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89104684112162734105946837 2088391033878814080608129)
                      ·
                        rfl

theorem cell23_4067127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_4067127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067127 prefixEnd_4067127 := by exact prefixLift 4067127
  have htrace : WordTrace (prefixWord ++ tailWord_4067127) baseStart_4067127 baseEnd_4067127 := by
    simpa [prefixWord, tailWord_4067127, baseEnd_4067127] using wordTrace_append hprefix tailTrace_4067127
  have hstable : (prefixWord ++ tailWord_4067127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067127).length < 2 ^ (prefixWord ++ tailWord_4067127).sum := by decide
  have hdescent : baseEnd_4067127 < baseStart_4067127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067198 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_4067198 : Nat := 118140960795 + 4067198 * 2 ^ 59
def prefixEnd_4067198 : Nat := 4983230072969 + 3 ^ 40 * 4067198 * 2
def baseEnd_4067198 : Nat := 696142497001761100940101

theorem tailTrace_4067198 : CollatzResearch.WordTrace tailWord_4067198 prefixEnd_4067198 696142497001761100940101 := by
  unfold tailWord_4067198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542862239905467870227281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98895265279495828641212165 18542862239905467870227281)
  ·
    refine ⟨13907146679929100902670461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18542862239905467870227281 13907146679929100902670461)
    ·
      refine ⟨5215180004973412838501423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13907146679929100902670461 5215180004973412838501423)
      ·
        refine ⟨7822770007460119257752135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215180004973412838501423 7822770007460119257752135)
        ·
          refine ⟨11734155011190178886628203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7822770007460119257752135 11734155011190178886628203)
          ·
            refine ⟨17601232516785268329942305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11734155011190178886628203 17601232516785268329942305)
            ·
              refine ⟨13200924387588951247456729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17601232516785268329942305 13200924387588951247456729)
              ·
                refine ⟨9900693290691713435592547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13200924387588951247456729 9900693290691713435592547)
                ·
                  refine ⟨14851039936037570153388821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9900693290691713435592547 14851039936037570153388821)
                  ·
                    refine ⟨696142497001761100940101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14851039936037570153388821 696142497001761100940101)
                    ·
                      rfl

theorem cell23_4067198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_4067198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067198 prefixEnd_4067198 := by exact prefixLift 4067198
  have htrace : WordTrace (prefixWord ++ tailWord_4067198) baseStart_4067198 baseEnd_4067198 := by
    simpa [prefixWord, tailWord_4067198, baseEnd_4067198] using wordTrace_append hprefix tailTrace_4067198
  have hstable : (prefixWord ++ tailWord_4067198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067198).length < 2 ^ (prefixWord ++ tailWord_4067198).sum := by decide
  have hdescent : baseEnd_4067198 < baseStart_4067198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067289 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 2, 1, 3]
def baseStart_4067289 : Nat := 118140960795 + 4067289 * 2 ^ 59
def prefixEnd_4067289 : Nat := 4983230072969 + 3 ^ 40 * 4067289 * 2
def baseEnd_4067289 : Nat := 2088474217744842446782385

theorem tailTrace_4067289 : CollatzResearch.WordTrace tailWord_4067289 prefixEnd_4067289 2088474217744842446782385 := by
  unfold tailWord_4067289
  simp only [CollatzResearch.WordTrace]
  refine ⟨148346216961914065503380921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98897477974609377002253947 148346216961914065503380921)
  ·
    refine ⟨111259662721435549127535691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148346216961914065503380921 111259662721435549127535691)
    ·
      refine ⟨166889494082153323691303537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111259662721435549127535691 166889494082153323691303537)
      ·
        refine ⟨125167120561614992768477653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166889494082153323691303537 125167120561614992768477653)
        ·
          refine ⟨2933604388162851393011195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125167120561614992768477653 2933604388162851393011195)
          ·
            refine ⟨4400406582244277089516793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933604388162851393011195 4400406582244277089516793)
            ·
              refine ⟨3300304936683207817137595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400406582244277089516793 3300304936683207817137595)
              ·
                refine ⟨4950457405024811725706393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300304936683207817137595 4950457405024811725706393)
                ·
                  refine ⟨3712843053768608794279795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4950457405024811725706393 3712843053768608794279795)
                  ·
                    refine ⟨5569264580652913191419693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712843053768608794279795 5569264580652913191419693)
                    ·
                      refine ⟨2088474217744842446782385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5569264580652913191419693 2088474217744842446782385)
                      ·
                        rfl

theorem cell23_4067289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_4067289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067289 prefixEnd_4067289 := by exact prefixLift 4067289
  have htrace : WordTrace (prefixWord ++ tailWord_4067289) baseStart_4067289 baseEnd_4067289 := by
    simpa [prefixWord, tailWord_4067289, baseEnd_4067289] using wordTrace_append hprefix tailTrace_4067289
  have hstable : (prefixWord ++ tailWord_4067289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067289).length < 2 ^ (prefixWord ++ tailWord_4067289).sum := by decide
  have hdescent : baseEnd_4067289 < baseStart_4067289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067335 : List Nat := [1, 1, 4, 3, 1, 2, 4, 2, 5]
def baseStart_4067335 : Nat := 118140960795 + 4067335 * 2 ^ 59
def prefixEnd_4067335 : Nat := 4983230072969 + 3 ^ 40 * 4067335 * 2
def baseEnd_4067335 : Nat := 232055315317216585200797

theorem tailTrace_4067335 : CollatzResearch.WordTrace tailWord_4067335 prefixEnd_4067335 232055315317216585200797 := by
  unfold tailWord_4067335
  simp only [CollatzResearch.WordTrace]
  refine ⟨148347894719747415359555459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98898596479831610239703639 148347894719747415359555459)
  ·
    refine ⟨222521842079621123039333189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148347894719747415359555459 222521842079621123039333189)
    ·
      refine ⟨41722845389928960569874973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222521842079621123039333189 41722845389928960569874973)
      ·
        refine ⟨15646067021223360213703115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41722845389928960569874973 15646067021223360213703115)
        ·
          refine ⟨23469100531835040320554673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15646067021223360213703115 23469100531835040320554673)
          ·
            refine ⟨17601825398876280240416005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23469100531835040320554673 17601825398876280240416005)
            ·
              refine ⟨3300342262289302545078001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17601825398876280240416005 3300342262289302545078001)
              ·
                refine ⟨2475256696716976908808501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3300342262289302545078001 2475256696716976908808501)
                ·
                  refine ⟨232055315317216585200797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2475256696716976908808501 232055315317216585200797)
                  ·
                    rfl

theorem cell23_4067335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 5].length) (baseStart_4067335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067335 prefixEnd_4067335 := by exact prefixLift 4067335
  have htrace : WordTrace (prefixWord ++ tailWord_4067335) baseStart_4067335 baseEnd_4067335 := by
    simpa [prefixWord, tailWord_4067335, baseEnd_4067335] using wordTrace_append hprefix tailTrace_4067335
  have hstable : (prefixWord ++ tailWord_4067335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067335).length < 2 ^ (prefixWord ++ tailWord_4067335).sum := by decide
  have hdescent : baseEnd_4067335 < baseStart_4067335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067381 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4067381 : Nat := 118140960795 + 4067381 * 2 ^ 59
def prefixEnd_4067381 : Nat := 4983230072969 + 3 ^ 40 * 4067381 * 2
def baseEnd_4067381 : Nat := 2088521457965056086831961

theorem tailTrace_4067381 : CollatzResearch.WordTrace tailWord_4067381 prefixEnd_4067381 2088521457965056086831961 := by
  unfold tailWord_4067381
  simp only [CollatzResearch.WordTrace]
  refine ⟨148349572477580765215729997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98899714985053843477153331 148349572477580765215729997)
  ·
    refine ⟨55631089679092786955898749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148349572477580765215729997 55631089679092786955898749)
    ·
      refine ⟨20861658629659795108462031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55631089679092786955898749 20861658629659795108462031)
      ·
        refine ⟨31292487944489692662693047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20861658629659795108462031 31292487944489692662693047)
        ·
          refine ⟨46938731916734538994039571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31292487944489692662693047 46938731916734538994039571)
          ·
            refine ⟨70408097875101808491059357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46938731916734538994039571 70408097875101808491059357)
            ·
              refine ⟨26403036703163178184147259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70408097875101808491059357 26403036703163178184147259)
              ·
                refine ⟨39604555054744767276220889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26403036703163178184147259 39604555054744767276220889)
                ·
                  refine ⟨29703416291058575457165667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39604555054744767276220889 29703416291058575457165667)
                  ·
                    refine ⟨44555124436587863185748501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29703416291058575457165667 44555124436587863185748501)
                    ·
                      refine ⟨2088521457965056086831961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44555124436587863185748501 2088521457965056086831961)
                      ·
                        rfl

theorem cell23_4067381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4067381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067381 prefixEnd_4067381 := by exact prefixLift 4067381
  have htrace : WordTrace (prefixWord ++ tailWord_4067381) baseStart_4067381 baseEnd_4067381 := by
    simpa [prefixWord, tailWord_4067381, baseEnd_4067381] using wordTrace_append hprefix tailTrace_4067381
  have hstable : (prefixWord ++ tailWord_4067381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067381).length < 2 ^ (prefixWord ++ tailWord_4067381).sum := by decide
  have hdescent : baseEnd_4067381 < baseStart_4067381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067388 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_4067388 : Nat := 118140960795 + 4067388 * 2 ^ 59
def prefixEnd_4067388 : Nat := 4983230072969 + 3 ^ 40 * 4067388 * 2
def baseEnd_4067388 : Nat := 2088525052329637559444429

theorem tailTrace_4067388 : CollatzResearch.WordTrace tailWord_4067388 prefixEnd_4067388 2088525052329637559444429 := by
  unfold tailWord_4067388
  simp only [CollatzResearch.WordTrace]
  refine ⟨74174913894277702705617409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98899885192370270274156545 74174913894277702705617409)
  ·
    refine ⟨55631185420708277029213057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74174913894277702705617409 55631185420708277029213057)
    ·
      refine ⟨41723389065531207771909793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55631185420708277029213057 41723389065531207771909793)
      ·
        refine ⟨31292541799148405828932345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41723389065531207771909793 31292541799148405828932345)
        ·
          refine ⟨23469406349361304371699259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31292541799148405828932345 23469406349361304371699259)
          ·
            refine ⟨35204109524041956557548889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23469406349361304371699259 35204109524041956557548889)
            ·
              refine ⟨26403082143031467418161667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35204109524041956557548889 26403082143031467418161667)
              ·
                refine ⟨39604623214547201127242501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26403082143031467418161667 39604623214547201127242501)
                ·
                  refine ⟨7425866852727600211357969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39604623214547201127242501 7425866852727600211357969)
                  ·
                    refine ⟨5569400139545700158518477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7425866852727600211357969 5569400139545700158518477)
                    ·
                      refine ⟨2088525052329637559444429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5569400139545700158518477 2088525052329637559444429)
                      ·
                        rfl

theorem cell23_4067388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_4067388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067388 prefixEnd_4067388 := by exact prefixLift 4067388
  have htrace : WordTrace (prefixWord ++ tailWord_4067388) baseStart_4067388 baseEnd_4067388 := by
    simpa [prefixWord, tailWord_4067388, baseEnd_4067388] using wordTrace_append hprefix tailTrace_4067388
  have hstable : (prefixWord ++ tailWord_4067388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067388).length < 2 ^ (prefixWord ++ tailWord_4067388).sum := by decide
  have hdescent : baseEnd_4067388 < baseStart_4067388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067452 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_4067452 : Nat := 118140960795 + 4067452 * 2 ^ 59
def prefixEnd_4067452 : Nat := 4983230072969 + 3 ^ 40 * 4067452 * 2
def baseEnd_4067452 : Nat := 2088557915091525309044135

theorem tailTrace_4067452 : CollatzResearch.WordTrace tailWord_4067452 prefixEnd_4067452 2088557915091525309044135 := by
  unfold tailWord_4067452
  simp only [CollatzResearch.WordTrace]
  refine ⟨74176081030161772170782305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98901441373549029561043073 74176081030161772170782305)
  ·
    refine ⟨55632060772621329128086729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74176081030161772170782305 55632060772621329128086729)
    ·
      refine ⟨41724045579465996846065047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55632060772621329128086729 41724045579465996846065047)
      ·
        refine ⟨62586068369198995269097571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41724045579465996846065047 62586068369198995269097571)
        ·
          refine ⟨93879102553798492903646357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62586068369198995269097571 93879102553798492903646357)
          ·
            refine ⟨4400582932209304354858423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93879102553798492903646357 4400582932209304354858423)
            ·
              refine ⟨6600874398313956532287635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400582932209304354858423 6600874398313956532287635)
              ·
                refine ⟨9901311597470934798431453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6600874398313956532287635 9901311597470934798431453)
                ·
                  refine ⟨3712991849051600549411795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9901311597470934798431453 3712991849051600549411795)
                  ·
                    refine ⟨5569487773577400824117693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3712991849051600549411795 5569487773577400824117693)
                    ·
                      refine ⟨2088557915091525309044135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5569487773577400824117693 2088557915091525309044135)
                      ·
                        rfl

theorem cell23_4067452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_4067452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067452 prefixEnd_4067452 := by exact prefixLift 4067452
  have htrace : WordTrace (prefixWord ++ tailWord_4067452) baseStart_4067452 baseEnd_4067452 := by
    simpa [prefixWord, tailWord_4067452, baseEnd_4067452] using wordTrace_append hprefix tailTrace_4067452
  have hstable : (prefixWord ++ tailWord_4067452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067452).length < 2 ^ (prefixWord ++ tailWord_4067452).sum := by decide
  have hdescent : baseEnd_4067452 < baseStart_4067452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067471 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_4067471 : Nat := 118140960795 + 4067471 * 2 ^ 59
def prefixEnd_4067471 : Nat := 4983230072969 + 3 ^ 40 * 4067471 * 2
def baseEnd_4067471 : Nat := 2088567671223960734706547

theorem tailTrace_4067471 : CollatzResearch.WordTrace tailWord_4067471 prefixEnd_4067471 2088567671223960734706547 := by
  unfold tailWord_4067471
  simp only [CollatzResearch.WordTrace]
  refine ⟨148352855047254710586506267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98901903364836473724337511 148352855047254710586506267)
  ·
    refine ⟨222529282570882065879759401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148352855047254710586506267 222529282570882065879759401)
    ·
      refine ⟨166896961928161549409819551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222529282570882065879759401 166896961928161549409819551)
      ·
        refine ⟨250345442892242324114729327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166896961928161549409819551 250345442892242324114729327)
        ·
          refine ⟨375518164338363486172093991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250345442892242324114729327 375518164338363486172093991)
          ·
            refine ⟨563277246507545229258140987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375518164338363486172093991 563277246507545229258140987)
            ·
              refine ⟨844915869761317843887211481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563277246507545229258140987 844915869761317843887211481)
              ·
                refine ⟨633686902320988382915408611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844915869761317843887211481 633686902320988382915408611)
                ·
                  refine ⟨950530353481482574373112917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633686902320988382915408611 950530353481482574373112917)
                  ·
                    refine ⟨11139027579861123918434917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 950530353481482574373112917 11139027579861123918434917)
                    ·
                      refine ⟨2088567671223960734706547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11139027579861123918434917 2088567671223960734706547)
                      ·
                        rfl

theorem cell23_4067471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_4067471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067471 prefixEnd_4067471 := by exact prefixLift 4067471
  have htrace : WordTrace (prefixWord ++ tailWord_4067471) baseStart_4067471 baseEnd_4067471 := by
    simpa [prefixWord, tailWord_4067471, baseEnd_4067471] using wordTrace_append hprefix tailTrace_4067471
  have hstable : (prefixWord ++ tailWord_4067471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067471).length < 2 ^ (prefixWord ++ tailWord_4067471).sum := by decide
  have hdescent : baseEnd_4067471 < baseStart_4067471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067475 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 5, 2, 2]
def baseStart_4067475 : Nat := 118140960795 + 4067475 * 2 ^ 59
def prefixEnd_4067475 : Nat := 4983230072969 + 3 ^ 40 * 4067475 * 2
def baseEnd_4067475 : Nat := 2088569725146578719056529

theorem tailTrace_4067475 : CollatzResearch.WordTrace tailWord_4067475 prefixEnd_4067475 2088569725146578719056529 := by
  unfold tailWord_4067475
  simp only [CollatzResearch.WordTrace]
  refine ⟨148353000939240219269651879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98902000626160146179767919 148353000939240219269651879)
  ·
    refine ⟨222529501408860328904477819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148353000939240219269651879 222529501408860328904477819)
    ·
      refine ⟨333794252113290493356716729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222529501408860328904477819 333794252113290493356716729)
      ·
        refine ⟨250345689084967870017537547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333794252113290493356716729 250345689084967870017537547)
        ·
          refine ⟨375518533627451805026306321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250345689084967870017537547 375518533627451805026306321)
          ·
            refine ⟨281638900220588853769729741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375518533627451805026306321 281638900220588853769729741)
            ·
              refine ⟨105614587582720820163648653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281638900220588853769729741 105614587582720820163648653)
              ·
                refine ⟨39605470343520307561368245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105614587582720820163648653 39605470343520307561368245)
                ·
                  refine ⟨3713012844705028833878273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39605470343520307561368245 3713012844705028833878273)
                  ·
                    refine ⟨2784759633528771625408705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713012844705028833878273 2784759633528771625408705)
                    ·
                      refine ⟨2088569725146578719056529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2784759633528771625408705 2088569725146578719056529)
                      ·
                        rfl

theorem cell23_4067475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 2, 2].length) (baseStart_4067475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067475 prefixEnd_4067475 := by exact prefixLift 4067475
  have htrace : WordTrace (prefixWord ++ tailWord_4067475) baseStart_4067475 baseEnd_4067475 := by
    simpa [prefixWord, tailWord_4067475, baseEnd_4067475] using wordTrace_append hprefix tailTrace_4067475
  have hstable : (prefixWord ++ tailWord_4067475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067475).length < 2 ^ (prefixWord ++ tailWord_4067475).sum := by decide
  have hdescent : baseEnd_4067475 < baseStart_4067475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067488 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_4067488 : Nat := 118140960795 + 4067488 * 2 ^ 59
def prefixEnd_4067488 : Nat := 4983230072969 + 3 ^ 40 * 4067488 * 2
def baseEnd_4067488 : Nat := 2088576400395087168193969

theorem tailTrace_4067488 : CollatzResearch.WordTrace tailWord_4067488 prefixEnd_4067488 2088576400395087168193969 := by
  unfold tailWord_4067488
  simp only [CollatzResearch.WordTrace]
  refine ⟨74176737544096561244937559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98902316725462081659916745 74176737544096561244937559)
  ·
    refine ⟨111265106316144841867406339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74176737544096561244937559 111265106316144841867406339)
    ·
      refine ⟨166897659474217262801109509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111265106316144841867406339 166897659474217262801109509)
      ·
        refine ⟨31293311151415736775208033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166897659474217262801109509 31293311151415736775208033)
        ·
          refine ⟨23469983363561802581406025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31293311151415736775208033 23469983363561802581406025)
          ·
            refine ⟨17602487522671351936054519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23469983363561802581406025 17602487522671351936054519)
            ·
              refine ⟨26403731284007027904081779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17602487522671351936054519 26403731284007027904081779)
              ·
                refine ⟨39605596926010541856122669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26403731284007027904081779 39605596926010541856122669)
                ·
                  refine ⟨14852098847253953196046001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39605596926010541856122669 14852098847253953196046001)
                  ·
                    refine ⟨11139074135440464897034501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14852098847253953196046001 11139074135440464897034501)
                    ·
                      refine ⟨2088576400395087168193969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11139074135440464897034501 2088576400395087168193969)
                      ·
                        rfl

theorem cell23_4067488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_4067488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067488 prefixEnd_4067488 := by exact prefixLift 4067488
  have htrace : WordTrace (prefixWord ++ tailWord_4067488) baseStart_4067488 baseEnd_4067488 := by
    simpa [prefixWord, tailWord_4067488, baseEnd_4067488] using wordTrace_append hprefix tailTrace_4067488
  have hstable : (prefixWord ++ tailWord_4067488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067488).length < 2 ^ (prefixWord ++ tailWord_4067488).sum := by decide
  have hdescent : baseEnd_4067488 < baseStart_4067488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067498 : List Nat := [3, 1, 5, 1, 13]
def baseStart_4067498 : Nat := 118140960795 + 4067498 * 2 ^ 59
def prefixEnd_4067498 : Nat := 4983230072969 + 3 ^ 40 * 4067498 * 2
def baseEnd_4067498 : Nat := 2864995247190167529587

theorem tailTrace_4067498 : CollatzResearch.WordTrace tailWord_4067498 prefixEnd_4067498 2864995247190167529587 := by
  unfold tailWord_4067498
  simp only [CollatzResearch.WordTrace]
  refine ⟨37088459954539223549434787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98902559878771262798492765 37088459954539223549434787)
  ·
    refine ⟨55632689931808835324152181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37088459954539223549434787 55632689931808835324152181)
    ·
      refine ⟨5215564681107078311639267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55632689931808835324152181 5215564681107078311639267)
      ·
        refine ⟨7823347021660617467458901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215564681107078311639267 7823347021660617467458901)
        ·
          refine ⟨2864995247190167529587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7823347021660617467458901 2864995247190167529587)
          ·
            rfl

theorem cell23_4067498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 13].length) (baseStart_4067498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067498 prefixEnd_4067498 := by exact prefixLift 4067498
  have htrace : WordTrace (prefixWord ++ tailWord_4067498) baseStart_4067498 baseEnd_4067498 := by
    simpa [prefixWord, tailWord_4067498, baseEnd_4067498] using wordTrace_append hprefix tailTrace_4067498
  have hstable : (prefixWord ++ tailWord_4067498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067498).length < 2 ^ (prefixWord ++ tailWord_4067498).sum := by decide
  have hdescent : baseEnd_4067498 < baseStart_4067498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067532 : List Nat := [2, 2, 1, 6, 1, 1, 3, 7]
def baseStart_4067532 : Nat := 118140960795 + 4067532 * 2 ^ 59
def prefixEnd_4067532 : Nat := 4983230072969 + 3 ^ 40 * 4067532 * 2
def baseEnd_4067532 : Nat := 77355518279403148001621

theorem tailTrace_4067532 : CollatzResearch.WordTrace tailWord_4067532 prefixEnd_4067532 77355518279403148001621 := by
  unfold tailWord_4067532
  simp only [CollatzResearch.WordTrace]
  refine ⟨74177539950016859002238425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98903386600022478669651233 74177539950016859002238425)
  ·
    refine ⟨55633154962512644251678819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74177539950016859002238425 55633154962512644251678819)
    ·
      refine ⟨83449732443768966377518229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55633154962512644251678819 83449732443768966377518229)
      ·
        refine ⟨3911706208301670298946167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83449732443768966377518229 3911706208301670298946167)
        ·
          refine ⟨5867559312452505448419251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3911706208301670298946167 5867559312452505448419251)
          ·
            refine ⟨8801338968678758172628877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5867559312452505448419251 8801338968678758172628877)
            ·
              refine ⟨3300502113254534314735829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8801338968678758172628877 3300502113254534314735829)
              ·
                refine ⟨77355518279403148001621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3300502113254534314735829 77355518279403148001621)
                ·
                  rfl

theorem cell23_4067532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 7].length) (baseStart_4067532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067532 prefixEnd_4067532 := by exact prefixLift 4067532
  have htrace : WordTrace (prefixWord ++ tailWord_4067532) baseStart_4067532 baseEnd_4067532 := by
    simpa [prefixWord, tailWord_4067532, baseEnd_4067532] using wordTrace_append hprefix tailTrace_4067532
  have hstable : (prefixWord ++ tailWord_4067532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067532).length < 2 ^ (prefixWord ++ tailWord_4067532).sum := by decide
  have hdescent : baseEnd_4067532 < baseStart_4067532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067535 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 3, 3, 2]
def baseStart_4067535 : Nat := 118140960795 + 4067535 * 2 ^ 59
def prefixEnd_4067535 : Nat := 4983230072969 + 3 ^ 40 * 4067535 * 2
def baseEnd_4067535 : Nat := 2088600533985848484306253

theorem tailTrace_4067535 : CollatzResearch.WordTrace tailWord_4067535 prefixEnd_4067535 2088600533985848484306253 := by
  unfold tailWord_4067535
  simp only [CollatzResearch.WordTrace]
  refine ⟨148355189319022849516836059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98903459546015233011224039 148355189319022849516836059)
  ·
    refine ⟨222532783978534274275254089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148355189319022849516836059 222532783978534274275254089)
    ·
      refine ⟨166899587983900705706440567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222532783978534274275254089 166899587983900705706440567)
      ·
        refine ⟨250349381975851058559660851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166899587983900705706440567 250349381975851058559660851)
        ·
          refine ⟨375524072963776587839491277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250349381975851058559660851 375524072963776587839491277)
          ·
            refine ⟨140821527361416220439809229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375524072963776587839491277 140821527361416220439809229)
            ·
              refine ⟨52808072760531082664928461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140821527361416220439809229 52808072760531082664928461)
              ·
                refine ⟨19803027285199155999348173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52808072760531082664928461 19803027285199155999348173)
                ·
                  refine ⟨7426135231949683499755565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19803027285199155999348173 7426135231949683499755565)
                  ·
                    refine ⟨2784800711981131312408337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7426135231949683499755565 2784800711981131312408337)
                    ·
                      refine ⟨2088600533985848484306253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2784800711981131312408337 2088600533985848484306253)
                      ·
                        rfl

theorem cell23_4067535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 3, 2].length) (baseStart_4067535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067535 prefixEnd_4067535 := by exact prefixLift 4067535
  have htrace : WordTrace (prefixWord ++ tailWord_4067535) baseStart_4067535 baseEnd_4067535 := by
    simpa [prefixWord, tailWord_4067535, baseEnd_4067535] using wordTrace_append hprefix tailTrace_4067535
  have hstable : (prefixWord ++ tailWord_4067535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067535).length < 2 ^ (prefixWord ++ tailWord_4067535).sum := by decide
  have hdescent : baseEnd_4067535 < baseStart_4067535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067552 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 1, 3, 2]
def baseStart_4067552 : Nat := 118140960795 + 4067552 * 2 ^ 59
def prefixEnd_4067552 : Nat := 4983230072969 + 3 ^ 40 * 4067552 * 2
def baseEnd_4067552 : Nat := 2088609263156974917793675

theorem tailTrace_4067552 : CollatzResearch.WordTrace tailWord_4067552 prefixEnd_4067552 2088609263156974917793675 := by
  unfold tailWord_4067552
  simp only [CollatzResearch.WordTrace]
  refine ⟨74177904679980630710102455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98903872906640840946803273 74177904679980630710102455)
  ·
    refine ⟨111266857019970946065153683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74177904679980630710102455 111266857019970946065153683)
    ·
      refine ⟨166900285529956419097730525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111266857019970946065153683 166900285529956419097730525)
      ·
        refine ⟨62587607073733657161648947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166900285529956419097730525 62587607073733657161648947)
        ·
          refine ⟨93881410610600485742473421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62587607073733657161648947 93881410610600485742473421)
          ·
            refine ⟨35205528978975182153427533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93881410610600485742473421 35205528978975182153427533)
            ·
              refine ⟨13202073367115693307535325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35205528978975182153427533 13202073367115693307535325)
              ·
                refine ⟨4950777512668384990325747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13202073367115693307535325 4950777512668384990325747)
                ·
                  refine ⟨7426166269002577485488621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950777512668384990325747 7426166269002577485488621)
                  ·
                    refine ⟨2784812350875966557058233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7426166269002577485488621 2784812350875966557058233)
                    ·
                      refine ⟨2088609263156974917793675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2784812350875966557058233 2088609263156974917793675)
                      ·
                        rfl

theorem cell23_4067552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_4067552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067552 prefixEnd_4067552 := by exact prefixLift 4067552
  have htrace : WordTrace (prefixWord ++ tailWord_4067552) baseStart_4067552 baseEnd_4067552 := by
    simpa [prefixWord, tailWord_4067552, baseEnd_4067552] using wordTrace_append hprefix tailTrace_4067552
  have hstable : (prefixWord ++ tailWord_4067552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067552).length < 2 ^ (prefixWord ++ tailWord_4067552).sum := by decide
  have hdescent : baseEnd_4067552 < baseStart_4067552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067559 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4067559 : Nat := 118140960795 + 4067559 * 2 ^ 59
def prefixEnd_4067559 : Nat := 4983230072969 + 3 ^ 40 * 4067559 * 2
def baseEnd_4067559 : Nat := 2088612857521556390406143

theorem tailTrace_4067559 : CollatzResearch.WordTrace tailWord_4067559 prefixEnd_4067559 2088612857521556390406143 := by
  unfold tailWord_4067559
  simp only [CollatzResearch.WordTrace]
  refine ⟨148356064670935901615709731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98904043113957267743806487 148356064670935901615709731)
  ·
    refine ⟨222534097006403852423564597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148356064670935901615709731 222534097006403852423564597)
    ·
      refine ⟨20862571594350361164709181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222534097006403852423564597 20862571594350361164709181)
      ·
        refine ⟨7823464347881385436765943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20862571594350361164709181 7823464347881385436765943)
        ·
          refine ⟨11735196521822078155148915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7823464347881385436765943 11735196521822078155148915)
          ·
            refine ⟨17602794782733117232723373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11735196521822078155148915 17602794782733117232723373)
            ·
              refine ⟨6601048043524918962271265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17602794782733117232723373 6601048043524918962271265)
              ·
                refine ⟨4950786032643689221703449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601048043524918962271265 4950786032643689221703449)
                ·
                  refine ⟨3713089524482766916277587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4950786032643689221703449 3713089524482766916277587)
                  ·
                    refine ⟨5569634286724150374416381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3713089524482766916277587 5569634286724150374416381)
                    ·
                      refine ⟨2088612857521556390406143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5569634286724150374416381 2088612857521556390406143)
                      ·
                        rfl

theorem cell23_4067559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4067559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067559 prefixEnd_4067559 := by exact prefixLift 4067559
  have htrace : WordTrace (prefixWord ++ tailWord_4067559) baseStart_4067559 baseEnd_4067559 := by
    simpa [prefixWord, tailWord_4067559, baseEnd_4067559] using wordTrace_append hprefix tailTrace_4067559
  have hstable : (prefixWord ++ tailWord_4067559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067559).length < 2 ^ (prefixWord ++ tailWord_4067559).sum := by decide
  have hdescent : baseEnd_4067559 < baseStart_4067559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067568 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 3]
def baseStart_4067568 : Nat := 118140960795 + 4067568 * 2 ^ 59
def prefixEnd_4067568 : Nat := 4983230072969 + 3 ^ 40 * 4067568 * 2
def baseEnd_4067568 : Nat := 2088617478847446855193601

theorem tailTrace_4067568 : CollatzResearch.WordTrace tailWord_4067568 prefixEnd_4067568 2088617478847446855193601 := by
  unfold tailWord_4067568
  simp only [CollatzResearch.WordTrace]
  refine ⟨74178196463951648076393679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98904261951935530768524905 74178196463951648076393679)
  ·
    refine ⟨111267294695927472114590519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74178196463951648076393679 111267294695927472114590519)
    ·
      refine ⟨166900942043891208171885779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111267294695927472114590519 166900942043891208171885779)
      ·
        refine ⟨250351413065836812257828669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166900942043891208171885779 250351413065836812257828669)
        ·
          refine ⟨93881779899688804596685751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250351413065836812257828669 93881779899688804596685751)
          ·
            refine ⟨140822669849533206895028627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93881779899688804596685751 140822669849533206895028627)
            ·
              refine ⟨211234004774299810342542941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140822669849533206895028627 211234004774299810342542941)
              ·
                refine ⟨79212751790362428878453603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211234004774299810342542941 79212751790362428878453603)
                ·
                  refine ⟨118819127685543643317680405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79212751790362428878453603 118819127685543643317680405)
                  ·
                    refine ⟨5569646610259858280516269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118819127685543643317680405 5569646610259858280516269)
                    ·
                      refine ⟨2088617478847446855193601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5569646610259858280516269 2088617478847446855193601)
                      ·
                        rfl

theorem cell23_4067568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_4067568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067568 prefixEnd_4067568 := by exact prefixLift 4067568
  have htrace : WordTrace (prefixWord ++ tailWord_4067568) baseStart_4067568 baseEnd_4067568 := by
    simpa [prefixWord, tailWord_4067568, baseEnd_4067568] using wordTrace_append hprefix tailTrace_4067568
  have hstable : (prefixWord ++ tailWord_4067568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067568).length < 2 ^ (prefixWord ++ tailWord_4067568).sum := by decide
  have hdescent : baseEnd_4067568 < baseStart_4067568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067586 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_4067586 : Nat := 118140960795 + 4067586 * 2 ^ 59
def prefixEnd_4067586 : Nat := 4983230072969 + 3 ^ 40 * 4067586 * 2
def baseEnd_4067586 : Nat := 2088626721499227784768519

theorem tailTrace_4067586 : CollatzResearch.WordTrace tailWord_4067586 prefixEnd_4067586 2088626721499227784768519 := by
  unfold tailWord_4067586
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089262360459521306735653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98904699627892056817961741 37089262360459521306735653)
  ·
    refine ⟨6954236692586160245012935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37089262360459521306735653 6954236692586160245012935)
    ·
      refine ⟨10431355038879240367519403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6954236692586160245012935 10431355038879240367519403)
      ·
        refine ⟨15647032558318860551279105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10431355038879240367519403 15647032558318860551279105)
        ·
          refine ⟨11735274418739145413459329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15647032558318860551279105 11735274418739145413459329)
          ·
            refine ⟨8801455814054359060094497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11735274418739145413459329 8801455814054359060094497)
            ·
              refine ⟨6601091860540769295070873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8801455814054359060094497 6601091860540769295070873)
              ·
                refine ⟨4950818895405576971303155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601091860540769295070873 4950818895405576971303155)
                ·
                  refine ⟨7426228343108365456954733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4950818895405576971303155 7426228343108365456954733)
                  ·
                    refine ⟨2784835628665637046358025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7426228343108365456954733 2784835628665637046358025)
                    ·
                      refine ⟨2088626721499227784768519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2784835628665637046358025 2088626721499227784768519)
                      ·
                        rfl

theorem cell23_4067586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_4067586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067586 prefixEnd_4067586 := by exact prefixLift 4067586
  have htrace : WordTrace (prefixWord ++ tailWord_4067586) baseStart_4067586 baseEnd_4067586 := by
    simpa [prefixWord, tailWord_4067586, baseEnd_4067586] using wordTrace_append hprefix tailTrace_4067586
  have hstable : (prefixWord ++ tailWord_4067586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067586).length < 2 ^ (prefixWord ++ tailWord_4067586).sum := by decide
  have hdescent : baseEnd_4067586 < baseStart_4067586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067628 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_4067628 : Nat := 118140960795 + 4067628 * 2 ^ 59
def prefixEnd_4067628 : Nat := 4983230072969 + 3 ^ 40 * 4067628 * 2
def baseEnd_4067628 : Nat := 2088648287686716620443325

theorem tailTrace_4067628 : CollatzResearch.WordTrace tailWord_4067628 prefixEnd_4067628 2088648287686716620443325 := by
  unfold tailWord_4067628
  simp only [CollatzResearch.WordTrace]
  refine ⟨74179290653842963199985769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98905720871790617599981025 74179290653842963199985769)
  ·
    refine ⟨55634467990382222399989327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74179290653842963199985769 55634467990382222399989327)
    ·
      refine ⟨83451701985573333599983991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55634467990382222399989327 83451701985573333599983991)
      ·
        refine ⟨125177552978360000399975987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83451701985573333599983991 125177552978360000399975987)
        ·
          refine ⟨187766329467540000599963981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125177552978360000399975987 187766329467540000599963981)
          ·
            refine ⟨70412373550327500224986493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187766329467540000599963981 70412373550327500224986493)
            ·
              refine ⟨26404640081372812584369935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70412373550327500224986493 26404640081372812584369935)
              ·
                refine ⟨39606960122059218876554903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26404640081372812584369935 39606960122059218876554903)
                ·
                  refine ⟨59410440183088828314832355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39606960122059218876554903 59410440183088828314832355)
                  ·
                    refine ⟨89115660274633242472248533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59410440183088828314832355 89115660274633242472248533)
                    ·
                      refine ⟨2088648287686716620443325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89115660274633242472248533 2088648287686716620443325)
                      ·
                        rfl

theorem cell23_4067628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_4067628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067628 prefixEnd_4067628 := by exact prefixLift 4067628
  have htrace : WordTrace (prefixWord ++ tailWord_4067628) baseStart_4067628 baseEnd_4067628 := by
    simpa [prefixWord, tailWord_4067628, baseEnd_4067628] using wordTrace_append hprefix tailTrace_4067628
  have hstable : (prefixWord ++ tailWord_4067628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067628).length < 2 ^ (prefixWord ++ tailWord_4067628).sum := by decide
  have hdescent : baseEnd_4067628 < baseStart_4067628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067633 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 2, 2, 2]
def baseStart_4067633 : Nat := 118140960795 + 4067633 * 2 ^ 59
def prefixEnd_4067633 : Nat := 4983230072969 + 3 ^ 40 * 4067633 * 2
def baseEnd_4067633 : Nat := 2088650855089989100880803

theorem tailTrace_4067633 : CollatzResearch.WordTrace tailWord_4067633 prefixEnd_4067633 2088650855089989100880803 := by
  unfold tailWord_4067633
  simp only [CollatzResearch.WordTrace]
  refine ⟨148358763672667812253903553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98905842448445208169269035 148358763672667812253903553)
  ·
    refine ⟨111269072754500859190427665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148358763672667812253903553 111269072754500859190427665)
    ·
      refine ⟨83451804565875644392820749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111269072754500859190427665 83451804565875644392820749)
      ·
        refine ⟨31294426712203366647307781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83451804565875644392820749 31294426712203366647307781)
        ·
          refine ⟨5867705008538131246370209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31294426712203366647307781 5867705008538131246370209)
          ·
            refine ⟨4400778756403598434777657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5867705008538131246370209 4400778756403598434777657)
            ·
              refine ⟨3300584067302698826083243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400778756403598434777657 3300584067302698826083243)
              ·
                refine ⟨4950876100954048239124865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300584067302698826083243 4950876100954048239124865)
                ·
                  refine ⟨3713157075715536179343649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4950876100954048239124865 3713157075715536179343649)
                  ·
                    refine ⟨2784867806786652134507737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713157075715536179343649 2784867806786652134507737)
                    ·
                      refine ⟨2088650855089989100880803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2784867806786652134507737 2088650855089989100880803)
                      ·
                        rfl

theorem cell23_4067633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_4067633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067633 prefixEnd_4067633 := by exact prefixLift 4067633
  have htrace : WordTrace (prefixWord ++ tailWord_4067633) baseStart_4067633 baseEnd_4067633 := by
    simpa [prefixWord, tailWord_4067633, baseEnd_4067633] using wordTrace_append hprefix tailTrace_4067633
  have hstable : (prefixWord ++ tailWord_4067633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067633).length < 2 ^ (prefixWord ++ tailWord_4067633).sum := by decide
  have hdescent : baseEnd_4067633 < baseStart_4067633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067658 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_4067658 : Nat := 118140960795 + 4067658 * 2 ^ 59
def prefixEnd_4067658 : Nat := 4983230072969 + 3 ^ 40 * 4067658 * 2
def baseEnd_4067658 : Nat := 2088663692106351503068187

theorem tailTrace_4067658 : CollatzResearch.WordTrace tailWord_4067658 prefixEnd_4067658 2088663692106351503068187 := by
  unfold tailWord_4067658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37089918874394310380890907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98906450331718161015709085 37089918874394310380890907)
  ·
    refine ⟨55634878311591465571336361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37089918874394310380890907 55634878311591465571336361)
    ·
      refine ⟨41726158733693599178502271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55634878311591465571336361 41726158733693599178502271)
      ·
        refine ⟨62589238100540398767753407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41726158733693599178502271 62589238100540398767753407)
        ·
          refine ⟨93883857150810598151630111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62589238100540398767753407 93883857150810598151630111)
          ·
            refine ⟨140825785726215897227445167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93883857150810598151630111 140825785726215897227445167)
            ·
              refine ⟨211238678589323845841167751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140825785726215897227445167 211238678589323845841167751)
              ·
                refine ⟨316858017883985768761751627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211238678589323845841167751 316858017883985768761751627)
                ·
                  refine ⟨475287026825978653142627441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316858017883985768761751627 475287026825978653142627441)
                  ·
                    refine ⟨356465270119483989856970581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 475287026825978653142627441 356465270119483989856970581)
                    ·
                      refine ⟨2088663692106351503068187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 356465270119483989856970581 2088663692106351503068187)
                      ·
                        rfl

theorem cell23_4067658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_4067658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067658 prefixEnd_4067658 := by exact prefixLift 4067658
  have htrace : WordTrace (prefixWord ++ tailWord_4067658) baseStart_4067658 baseEnd_4067658 := by
    simpa [prefixWord, tailWord_4067658, baseEnd_4067658] using wordTrace_append hprefix tailTrace_4067658
  have hstable : (prefixWord ++ tailWord_4067658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067658).length < 2 ^ (prefixWord ++ tailWord_4067658).sum := by decide
  have hdescent : baseEnd_4067658 < baseStart_4067658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067709 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_4067709 : Nat := 118140960795 + 4067709 * 2 ^ 59
def prefixEnd_4067709 : Nat := 4983230072969 + 3 ^ 40 * 4067709 * 2
def baseEnd_4067709 : Nat := 2088689879619730803530453

theorem tailTrace_4067709 : CollatzResearch.WordTrace tailWord_4067709 prefixEnd_4067709 2088689879619730803530453 := by
  unfold tailWord_4067709
  simp only [CollatzResearch.WordTrace]
  refine ⟨148361535620392477233670181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98907690413594984822446787 148361535620392477233670181)
  ·
    refine ⟨27817787928823589481313159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148361535620392477233670181 27817787928823589481313159)
    ·
      refine ⟨41726681893235384221969739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27817787928823589481313159 41726681893235384221969739)
      ·
        refine ⟨62590022839853076332954609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41726681893235384221969739 62590022839853076332954609)
        ·
          refine ⟨46942517129889807249715957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62590022839853076332954609 46942517129889807249715957)
          ·
            refine ⟨4400860980927169429660871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46942517129889807249715957 4400860980927169429660871)
            ·
              refine ⟨6601291471390754144491307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400860980927169429660871 6601291471390754144491307)
              ·
                refine ⟨9901937207086131216736961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6601291471390754144491307 9901937207086131216736961)
                ·
                  refine ⟨7426452905314598412552721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9901937207086131216736961 7426452905314598412552721)
                  ·
                    refine ⟨5569839678985948809414541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7426452905314598412552721 5569839678985948809414541)
                    ·
                      refine ⟨2088689879619730803530453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5569839678985948809414541 2088689879619730803530453)
                      ·
                        rfl

theorem cell23_4067709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_4067709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067709 prefixEnd_4067709 := by exact prefixLift 4067709
  have htrace : WordTrace (prefixWord ++ tailWord_4067709) baseStart_4067709 baseEnd_4067709 := by
    simpa [prefixWord, tailWord_4067709, baseEnd_4067709] using wordTrace_append hprefix tailTrace_4067709
  have hstable : (prefixWord ++ tailWord_4067709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067709).length < 2 ^ (prefixWord ++ tailWord_4067709).sum := by decide
  have hdescent : baseEnd_4067709 < baseStart_4067709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067762 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_4067762 : Nat := 118140960795 + 4067762 * 2 ^ 59
def prefixEnd_4067762 : Nat := 4983230072969 + 3 ^ 40 * 4067762 * 2
def baseEnd_4067762 : Nat := 2088717094094419096167709

theorem tailTrace_4067762 : CollatzResearch.WordTrace tailWord_4067762 prefixEnd_4067762 2088717094094419096167709 := by
  unfold tailWord_4067762
  simp only [CollatzResearch.WordTrace]
  refine ⟨37090867172300116821337385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98908979126133644856899693 37090867172300116821337385)
  ·
    refine ⟨27818150379225087616003039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37090867172300116821337385 27818150379225087616003039)
    ·
      refine ⟨41727225568837631424004559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27818150379225087616003039 41727225568837631424004559)
      ·
        refine ⟨62590838353256447136006839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41727225568837631424004559 62590838353256447136006839)
        ·
          refine ⟨93886257529884670704010259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62590838353256447136006839 93886257529884670704010259)
          ·
            refine ⟨140829386294827006056015389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93886257529884670704010259 140829386294827006056015389)
            ·
              refine ⟨52811019860560127271005771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140829386294827006056015389 52811019860560127271005771)
              ·
                refine ⟨79216529790840190906508657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52811019860560127271005771 79216529790840190906508657)
                ·
                  refine ⟨59412397343130143179881493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79216529790840190906508657 59412397343130143179881493)
                  ·
                    refine ⟨2784956125459225461556945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59412397343130143179881493 2784956125459225461556945)
                    ·
                      refine ⟨2088717094094419096167709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2784956125459225461556945 2088717094094419096167709)
                      ·
                        rfl

theorem cell23_4067762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_4067762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067762 prefixEnd_4067762 := by exact prefixLift 4067762
  have htrace : WordTrace (prefixWord ++ tailWord_4067762) baseStart_4067762 baseEnd_4067762 := by
    simpa [prefixWord, tailWord_4067762, baseEnd_4067762] using wordTrace_append hprefix tailTrace_4067762
  have hstable : (prefixWord ++ tailWord_4067762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067762).length < 2 ^ (prefixWord ++ tailWord_4067762).sum := by decide
  have hdescent : baseEnd_4067762 < baseStart_4067762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067773 : List Nat := [1, 4, 1, 2, 2, 4, 1, 3, 1, 1, 3]
def baseStart_4067773 : Nat := 118140960795 + 4067773 * 2 ^ 59
def prefixEnd_4067773 : Nat := 4983230072969 + 3 ^ 40 * 4067773 * 2
def baseEnd_4067773 : Nat := 2088722742381618553130159

theorem tailTrace_4067773 : CollatzResearch.WordTrace tailWord_4067773 prefixEnd_4067773 2088722742381618553130159 := by
  unfold tailWord_4067773
  simp only [CollatzResearch.WordTrace]
  refine ⟨148363869892160616163999973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98909246594773744109333315 148363869892160616163999973)
  ·
    refine ⟨27818225604780115530749995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148363869892160616163999973 27818225604780115530749995)
    ·
      refine ⟨41727338407170173296124993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27818225604780115530749995 41727338407170173296124993)
      ·
        refine ⟨31295503805377629972093745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41727338407170173296124993 31295503805377629972093745)
        ·
          refine ⟨23471627854033222479070309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31295503805377629972093745 23471627854033222479070309)
          ·
            refine ⟨4400930222631229214825683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23471627854033222479070309 4400930222631229214825683)
            ·
              refine ⟨6601395333946843822238525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400930222631229214825683 6601395333946843822238525)
              ·
                refine ⟨2475523250230066433339447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6601395333946843822238525 2475523250230066433339447)
                ·
                  refine ⟨3713284875345099650009171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475523250230066433339447 3713284875345099650009171)
                  ·
                    refine ⟨5569927313017649475013757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3713284875345099650009171 5569927313017649475013757)
                    ·
                      refine ⟨2088722742381618553130159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5569927313017649475013757 2088722742381618553130159)
                      ·
                        rfl

theorem cell23_4067773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_4067773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067773 prefixEnd_4067773 := by exact prefixLift 4067773
  have htrace : WordTrace (prefixWord ++ tailWord_4067773) baseStart_4067773 baseEnd_4067773 := by
    simpa [prefixWord, tailWord_4067773, baseEnd_4067773] using wordTrace_append hprefix tailTrace_4067773
  have hstable : (prefixWord ++ tailWord_4067773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067773).length < 2 ^ (prefixWord ++ tailWord_4067773).sum := by decide
  have hdescent : baseEnd_4067773 < baseStart_4067773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067810 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4067810 : Nat := 118140960795 + 4067810 * 2 ^ 59
def prefixEnd_4067810 : Nat := 4983230072969 + 3 ^ 40 * 4067810 * 2
def baseEnd_4067810 : Nat := 696247247055278302789163

theorem tailTrace_4067810 : CollatzResearch.WordTrace tailWord_4067810 prefixEnd_4067810 696247247055278302789163 := by
  unfold tailWord_4067810
  simp only [CollatzResearch.WordTrace]
  refine ⟨37091304848256642870774221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98910146262017714322064589 37091304848256642870774221)
  ·
    refine ⟨13909239318096241076540333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37091304848256642870774221 13909239318096241076540333)
    ·
      refine ⟨5215964744286090403702625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13909239318096241076540333 5215964744286090403702625)
      ·
        refine ⟨3911973558214567802776969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5215964744286090403702625 3911973558214567802776969)
        ·
          refine ⟨2933980168660925852082727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3911973558214567802776969 2933980168660925852082727)
          ·
            refine ⟨4400970252991388778124091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933980168660925852082727 4400970252991388778124091)
            ·
              refine ⟨6601455379487083167186137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400970252991388778124091 6601455379487083167186137)
              ·
                refine ⟨4951091534615312375389603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601455379487083167186137 4951091534615312375389603)
                ·
                  refine ⟨7426637301922968563084405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951091534615312375389603 7426637301922968563084405)
                  ·
                    refine ⟨696247247055278302789163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7426637301922968563084405 696247247055278302789163)
                    ·
                      rfl

theorem cell23_4067810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4067810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067810 prefixEnd_4067810 := by exact prefixLift 4067810
  have htrace : WordTrace (prefixWord ++ tailWord_4067810) baseStart_4067810 baseEnd_4067810 := by
    simpa [prefixWord, tailWord_4067810, baseEnd_4067810] using wordTrace_append hprefix tailTrace_4067810
  have hstable : (prefixWord ++ tailWord_4067810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067810).length < 2 ^ (prefixWord ++ tailWord_4067810).sum := by decide
  have hdescent : baseEnd_4067810 < baseStart_4067810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067813 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 1, 1, 4]
def baseStart_4067813 : Nat := 118140960795 + 4067813 * 2 ^ 59
def prefixEnd_4067813 : Nat := 4983230072969 + 3 ^ 40 * 4067813 * 2
def baseEnd_4067813 : Nat := 2088743281607798396629975

theorem tailTrace_4067813 : CollatzResearch.WordTrace tailWord_4067813 prefixEnd_4067813 2088743281607798396629975 := by
  unfold tailWord_4067813
  simp only [CollatzResearch.WordTrace]
  refine ⟨148365328812015702995456093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98910219208010468663637395 148365328812015702995456093)
  ·
    refine ⟨55636998304505888623296035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148365328812015702995456093 55636998304505888623296035)
    ·
      refine ⟨83455497456758832934944053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55636998304505888623296035 83455497456758832934944053)
      ·
        refine ⟨7823952886571140587651005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83455497456758832934944053 7823952886571140587651005)
        ·
          refine ⟨2933982332464177720369127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7823952886571140587651005 2933982332464177720369127)
          ·
            refine ⟨4400973498696266580553691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933982332464177720369127 4400973498696266580553691)
            ·
              refine ⟨6601460248044399870830537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400973498696266580553691 6601460248044399870830537)
              ·
                refine ⟨4951095186033299903122903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601460248044399870830537 4951095186033299903122903)
                ·
                  refine ⟨7426642779049949854684355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951095186033299903122903 7426642779049949854684355)
                  ·
                    refine ⟨11139964168574924782026533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7426642779049949854684355 11139964168574924782026533)
                    ·
                      refine ⟨2088743281607798396629975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11139964168574924782026533 2088743281607798396629975)
                      ·
                        rfl

theorem cell23_4067813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_4067813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067813 prefixEnd_4067813 := by exact prefixLift 4067813
  have htrace : WordTrace (prefixWord ++ tailWord_4067813) baseStart_4067813 baseEnd_4067813 := by
    simpa [prefixWord, tailWord_4067813, baseEnd_4067813] using wordTrace_append hprefix tailTrace_4067813
  have hstable : (prefixWord ++ tailWord_4067813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067813).length < 2 ^ (prefixWord ++ tailWord_4067813).sum := by decide
  have hdescent : baseEnd_4067813 < baseStart_4067813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067816 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_4067816 : Nat := 118140960795 + 4067816 * 2 ^ 59
def prefixEnd_4067816 : Nat := 4983230072969 + 3 ^ 40 * 4067816 * 2
def baseEnd_4067816 : Nat := 2088744822049761884892461

theorem tailTrace_4067816 : CollatzResearch.WordTrace tailWord_4067816 prefixEnd_4067816 2088744822049761884892461 := by
  unfold tailWord_4067816
  simp only [CollatzResearch.WordTrace]
  refine ⟨74182719115502417253907651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98910292154003223005210201 74182719115502417253907651)
  ·
    refine ⟨111274078673253625880861477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74182719115502417253907651 111274078673253625880861477)
    ·
      refine ⟨20863889751235054852661527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111274078673253625880861477 20863889751235054852661527)
      ·
        refine ⟨31295834626852582278992291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20863889751235054852661527 31295834626852582278992291)
        ·
          refine ⟨46943751940278873418488437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31295834626852582278992291 46943751940278873418488437)
          ·
            refine ⟨4400976744401144382983291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46943751940278873418488437 4400976744401144382983291)
            ·
              refine ⟨6601465116601716574474937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400976744401144382983291 6601465116601716574474937)
              ·
                refine ⟨4951098837451287430856203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6601465116601716574474937 4951098837451287430856203)
                ·
                  refine ⟨7426648256176931146284305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951098837451287430856203 7426648256176931146284305)
                  ·
                    refine ⟨5569986192132698359713229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7426648256176931146284305 5569986192132698359713229)
                    ·
                      refine ⟨2088744822049761884892461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5569986192132698359713229 2088744822049761884892461)
                      ·
                        rfl

theorem cell23_4067816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_4067816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067816 prefixEnd_4067816 := by exact prefixLift 4067816
  have htrace : WordTrace (prefixWord ++ tailWord_4067816) baseStart_4067816 baseEnd_4067816 := by
    simpa [prefixWord, tailWord_4067816, baseEnd_4067816] using wordTrace_append hprefix tailTrace_4067816
  have hstable : (prefixWord ++ tailWord_4067816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067816).length < 2 ^ (prefixWord ++ tailWord_4067816).sum := by decide
  have hdescent : baseEnd_4067816 < baseStart_4067816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067835 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 4]
def baseStart_4067835 : Nat := 118140960795 + 4067835 * 2 ^ 59
def prefixEnd_4067835 : Nat := 4983230072969 + 3 ^ 40 * 4067835 * 2
def baseEnd_4067835 : Nat := 2088754578182197310554873

theorem tailTrace_4067835 : CollatzResearch.WordTrace tailWord_4067835 prefixEnd_4067835 2088754578182197310554873 := by
  unfold tailWord_4067835
  simp only [CollatzResearch.WordTrace]
  refine ⟨148366131217936000752756959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98910754145290667168504639 148366131217936000752756959)
  ·
    refine ⟨222549196826904001129135439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148366131217936000752756959 222549196826904001129135439)
    ·
      refine ⟨333823795240356001693703159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222549196826904001129135439 333823795240356001693703159)
      ·
        refine ⟨500735692860534002540554739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333823795240356001693703159 500735692860534002540554739)
        ·
          refine ⟨751103539290801003810832109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500735692860534002540554739 751103539290801003810832109)
          ·
            refine ⟨281663827234050376429062041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 751103539290801003810832109 281663827234050376429062041)
            ·
              refine ⟨211247870425537782321796531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281663827234050376429062041 211247870425537782321796531)
              ·
                refine ⟨316871805638306673482694797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211247870425537782321796531 316871805638306673482694797)
                ·
                  refine ⟨118826927114365002556010549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316871805638306673482694797 118826927114365002556010549)
                  ·
                    refine ⟨11140024416971718989625989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118826927114365002556010549 11140024416971718989625989)
                    ·
                      refine ⟨2088754578182197310554873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11140024416971718989625989 2088754578182197310554873)
                      ·
                        rfl

theorem cell23_4067835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 4].length) (baseStart_4067835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067835 prefixEnd_4067835 := by exact prefixLift 4067835
  have htrace : WordTrace (prefixWord ++ tailWord_4067835) baseStart_4067835 baseEnd_4067835 := by
    simpa [prefixWord, tailWord_4067835, baseEnd_4067835] using wordTrace_append hprefix tailTrace_4067835
  have hstable : (prefixWord ++ tailWord_4067835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067835).length < 2 ^ (prefixWord ++ tailWord_4067835).sum := by decide
  have hdescent : baseEnd_4067835 < baseStart_4067835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067847 : List Nat := [1, 1, 4, 3, 3, 2, 2, 2, 1, 2, 2]
def baseStart_4067847 : Nat := 118140960795 + 4067847 * 2 ^ 59
def prefixEnd_4067847 : Nat := 4983230072969 + 3 ^ 40 * 4067847 * 2
def baseEnd_4067847 : Nat := 2088760739950051263604819

theorem tailTrace_4067847 : CollatzResearch.WordTrace tailWord_4067847 prefixEnd_4067847 2088760739950051263604819 := by
  unfold tailWord_4067847
  simp only [CollatzResearch.WordTrace]
  refine ⟨148366568893892526802193795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98911045929261684534795863 148366568893892526802193795)
  ·
    refine ⟨222549853340838790203290693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148366568893892526802193795 222549853340838790203290693)
    ·
      refine ⟨41728097501407273163117005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222549853340838790203290693 41728097501407273163117005)
      ·
        refine ⟨15648036563027727436168877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41728097501407273163117005 15648036563027727436168877)
        ·
          refine ⟨5868013711135397788563329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15648036563027727436168877 5868013711135397788563329)
          ·
            refine ⟨4401010283351548341422497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5868013711135397788563329 4401010283351548341422497)
            ·
              refine ⟨3300757712513661256066873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4401010283351548341422497 3300757712513661256066873)
              ·
                refine ⟨2475568284385245942050155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3300757712513661256066873 2475568284385245942050155)
                ·
                  refine ⟨3713352426577868913075233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475568284385245942050155 3713352426577868913075233)
                  ·
                    refine ⟨2785014319933401684806425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3713352426577868913075233 2785014319933401684806425)
                    ·
                      refine ⟨2088760739950051263604819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785014319933401684806425 2088760739950051263604819)
                      ·
                        rfl

theorem cell23_4067847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_4067847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067847 prefixEnd_4067847 := by exact prefixLift 4067847
  have htrace : WordTrace (prefixWord ++ tailWord_4067847) baseStart_4067847 baseEnd_4067847 := by
    simpa [prefixWord, tailWord_4067847, baseEnd_4067847] using wordTrace_append hprefix tailTrace_4067847
  have hstable : (prefixWord ++ tailWord_4067847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067847).length < 2 ^ (prefixWord ++ tailWord_4067847).sum := by decide
  have hdescent : baseEnd_4067847 < baseStart_4067847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067852 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_4067852 : Nat := 118140960795 + 4067852 * 2 ^ 59
def prefixEnd_4067852 : Nat := 4983230072969 + 3 ^ 40 * 4067852 * 2
def baseEnd_4067852 : Nat := 2088763307353323744042295

theorem tailTrace_4067852 : CollatzResearch.WordTrace tailWord_4067852 prefixEnd_4067852 2088763307353323744042295 := by
  unfold tailWord_4067852
  simp only [CollatzResearch.WordTrace]
  refine ⟨74183375629437206328062905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98911167505916275104083873 74183375629437206328062905)
  ·
    refine ⟨55637531722077904746047179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74183375629437206328062905 55637531722077904746047179)
    ·
      refine ⟨83456297583116857119070769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55637531722077904746047179 83456297583116857119070769)
      ·
        refine ⟨62592223187337642839303077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83456297583116857119070769 62592223187337642839303077)
        ·
          refine ⟨11736041847625808032369327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62592223187337642839303077 11736041847625808032369327)
          ·
            refine ⟨17604062771438712048553991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11736041847625808032369327 17604062771438712048553991)
            ·
              refine ⟨26406094157158068072830987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17604062771438712048553991 26406094157158068072830987)
              ·
                refine ⟨39609141235737102109246481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26406094157158068072830987 39609141235737102109246481)
                ·
                  refine ⟨29706855926802826581934861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39609141235737102109246481 29706855926802826581934861)
                  ·
                    refine ⟨11140070972551059968225573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29706855926802826581934861 11140070972551059968225573)
                    ·
                      refine ⟨2088763307353323744042295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11140070972551059968225573 2088763307353323744042295)
                      ·
                        rfl

theorem cell23_4067852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_4067852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067852 prefixEnd_4067852 := by exact prefixLift 4067852
  have htrace : WordTrace (prefixWord ++ tailWord_4067852) baseStart_4067852 baseEnd_4067852 := by
    simpa [prefixWord, tailWord_4067852, baseEnd_4067852] using wordTrace_append hprefix tailTrace_4067852
  have hstable : (prefixWord ++ tailWord_4067852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067852).length < 2 ^ (prefixWord ++ tailWord_4067852).sum := by decide
  have hdescent : baseEnd_4067852 < baseStart_4067852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067855 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_4067855 : Nat := 118140960795 + 4067855 * 2 ^ 59
def prefixEnd_4067855 : Nat := 4983230072969 + 3 ^ 40 * 4067855 * 2
def baseEnd_4067855 : Nat := 2088764847795287232304781

theorem tailTrace_4067855 : CollatzResearch.WordTrace tailWord_4067855 prefixEnd_4067855 2088764847795287232304781 := by
  unfold tailWord_4067855
  simp only [CollatzResearch.WordTrace]
  refine ⟨148366860677863544168485019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98911240451909029445656679 148366860677863544168485019)
  ·
    refine ⟨222550291016795316252727529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148366860677863544168485019 222550291016795316252727529)
    ·
      refine ⟨166912718262596487189545647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222550291016795316252727529 166912718262596487189545647)
      ·
        refine ⟨250369077393894730784318471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166912718262596487189545647 250369077393894730784318471)
        ·
          refine ⟨375553616090842096176477707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250369077393894730784318471 375553616090842096176477707)
          ·
            refine ⟨563330424136263144264716561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375553616090842096176477707 563330424136263144264716561)
            ·
              refine ⟨422497818102197358198537421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563330424136263144264716561 422497818102197358198537421)
              ·
                refine ⟨158436681788324009324451533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422497818102197358198537421 158436681788324009324451533)
                ·
                  refine ⟨59413755670621503496669325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158436681788324009324451533 59413755670621503496669325)
                  ·
                    refine ⟨22280158376483063811250997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59413755670621503496669325 22280158376483063811250997)
                    ·
                      refine ⟨2088764847795287232304781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22280158376483063811250997 2088764847795287232304781)
                      ·
                        rfl

theorem cell23_4067855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_4067855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067855 prefixEnd_4067855 := by exact prefixLift 4067855
  have htrace : WordTrace (prefixWord ++ tailWord_4067855) baseStart_4067855 baseEnd_4067855 := by
    simpa [prefixWord, tailWord_4067855, baseEnd_4067855] using wordTrace_append hprefix tailTrace_4067855
  have hstable : (prefixWord ++ tailWord_4067855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067855).length < 2 ^ (prefixWord ++ tailWord_4067855).sum := by decide
  have hdescent : baseEnd_4067855 < baseStart_4067855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067865 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_4067865 : Nat := 118140960795 + 4067865 * 2 ^ 59
def prefixEnd_4067865 : Nat := 4983230072969 + 3 ^ 40 * 4067865 * 2
def baseEnd_4067865 : Nat := 2088769982601832193179735

theorem tailTrace_4067865 : CollatzResearch.WordTrace tailWord_4067865 prefixEnd_4067865 2088769982601832193179735 := by
  unfold tailWord_4067865
  simp only [CollatzResearch.WordTrace]
  refine ⟨148367225407827315876349049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98911483605218210584232699 148367225407827315876349049)
  ·
    refine ⟨111275419055870486907261787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148367225407827315876349049 111275419055870486907261787)
    ·
      refine ⟨166913128583805730360892681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111275419055870486907261787 166913128583805730360892681)
      ·
        refine ⟨125184846437854297770669511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166913128583805730360892681 125184846437854297770669511)
        ·
          refine ⟨187777269656781446656004267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125184846437854297770669511 187777269656781446656004267)
          ·
            refine ⟨281665904485172169984006401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187777269656781446656004267 281665904485172169984006401)
            ·
              refine ⟨211249428363879127488004801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281665904485172169984006401 211249428363879127488004801)
              ·
                refine ⟨158437071272909345616003601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211249428363879127488004801 158437071272909345616003601)
                ·
                  refine ⟨118827803454682009212002701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158437071272909345616003601 118827803454682009212002701)
                  ·
                    refine ⟨44560426295505753454501013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118827803454682009212002701 44560426295505753454501013)
                    ·
                      refine ⟨2088769982601832193179735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44560426295505753454501013 2088769982601832193179735)
                      ·
                        rfl

theorem cell23_4067865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_4067865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067865 prefixEnd_4067865 := by exact prefixLift 4067865
  have htrace : WordTrace (prefixWord ++ tailWord_4067865) baseStart_4067865 baseEnd_4067865 := by
    simpa [prefixWord, tailWord_4067865, baseEnd_4067865] using wordTrace_append hprefix tailTrace_4067865
  have hstable : (prefixWord ++ tailWord_4067865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067865).length < 2 ^ (prefixWord ++ tailWord_4067865).sum := by decide
  have hdescent : baseEnd_4067865 < baseStart_4067865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067909 : List Nat := [1, 3, 1, 1, 1, 5, 2, 4, 5]
def baseStart_4067909 : Nat := 118140960795 + 4067909 * 2 ^ 59
def prefixEnd_4067909 : Nat := 4983230072969 + 3 ^ 40 * 4067909 * 2
def baseEnd_4067909 : Nat := 232088063972292224558837

theorem tailTrace_4067909 : CollatzResearch.WordTrace tailWord_4067909 prefixEnd_4067909 232088063972292224558837 := by
  unfold tailWord_4067909
  simp only [CollatzResearch.WordTrace]
  refine ⟨148368830219667911390950781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98912553479778607593967187 148368830219667911390950781)
  ·
    refine ⟨55638311332375466771606543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148368830219667911390950781 55638311332375466771606543)
    ·
      refine ⟨83457466998563200157409815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55638311332375466771606543 83457466998563200157409815)
      ·
        refine ⟨125186200497844800236114723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83457466998563200157409815 125186200497844800236114723)
        ·
          refine ⟨187779300746767200354172085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125186200497844800236114723 187779300746767200354172085)
          ·
            refine ⟨17604309445009425033203633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187779300746767200354172085 17604309445009425033203633)
            ·
              refine ⟨13203232083757068774902725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17604309445009425033203633 13203232083757068774902725)
              ·
                refine ⟨2475606015704450395294261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13203232083757068774902725 2475606015704450395294261)
                ·
                  refine ⟨232088063972292224558837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2475606015704450395294261 232088063972292224558837)
                  ·
                    rfl

theorem cell23_4067909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_4067909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067909 prefixEnd_4067909 := by exact prefixLift 4067909
  have htrace : WordTrace (prefixWord ++ tailWord_4067909) baseStart_4067909 baseEnd_4067909 := by
    simpa [prefixWord, tailWord_4067909, baseEnd_4067909] using wordTrace_append hprefix tailTrace_4067909
  have hstable : (prefixWord ++ tailWord_4067909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067909).length < 2 ^ (prefixWord ++ tailWord_4067909).sum := by decide
  have hdescent : baseEnd_4067909 < baseStart_4067909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067922 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_4067922 : Nat := 118140960795 + 4067922 * 2 ^ 59
def prefixEnd_4067922 : Nat := 4983230072969 + 3 ^ 40 * 4067922 * 2
def baseEnd_4067922 : Nat := 696266416999712823388991

theorem tailTrace_4067922 : CollatzResearch.WordTrace tailWord_4067922 prefixEnd_4067922 696266416999712823388991 := by
  unfold tailWord_4067922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37092326092155203652793505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98912869579080543074116013 37092326092155203652793505)
  ·
    refine ⟨27819244569116402739595129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37092326092155203652793505 27819244569116402739595129)
    ·
      refine ⟨20864433426837302054696347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27819244569116402739595129 20864433426837302054696347)
      ·
        refine ⟨31296650140255953082044521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20864433426837302054696347 31296650140255953082044521)
        ·
          refine ⟨23472487605191964811533391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31296650140255953082044521 23472487605191964811533391)
          ·
            refine ⟨35208731407787947217300087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23472487605191964811533391 35208731407787947217300087)
            ·
              refine ⟨52813097111681920825950131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35208731407787947217300087 52813097111681920825950131)
              ·
                refine ⟨79219645667522881238925197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52813097111681920825950131 79219645667522881238925197)
                ·
                  refine ⟨29707367125321080464596949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79219645667522881238925197 29707367125321080464596949)
                  ·
                    refine ⟨696266416999712823388991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29707367125321080464596949 696266416999712823388991)
                    ·
                      rfl

theorem cell23_4067922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_4067922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067922 prefixEnd_4067922 := by exact prefixLift 4067922
  have htrace : WordTrace (prefixWord ++ tailWord_4067922) baseStart_4067922 baseEnd_4067922 := by
    simpa [prefixWord, tailWord_4067922, baseEnd_4067922] using wordTrace_append hprefix tailTrace_4067922
  have hstable : (prefixWord ++ tailWord_4067922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067922).length < 2 ^ (prefixWord ++ tailWord_4067922).sum := by decide
  have hdescent : baseEnd_4067922 < baseStart_4067922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067959 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 4, 4, 2]
def baseStart_4067959 : Nat := 118140960795 + 4067959 * 2 ^ 59
def prefixEnd_4067959 : Nat := 4983230072969 + 3 ^ 40 * 4067959 * 2
def baseEnd_4067959 : Nat := 2088818249783354825404303

theorem tailTrace_4067959 : CollatzResearch.WordTrace tailWord_4067959 prefixEnd_4067959 2088818249783354825404303 := by
  unfold tailWord_4067959
  simp only [CollatzResearch.WordTrace]
  refine ⟨148370653869486769930270931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98913769246324513286847287 148370653869486769930270931)
  ·
    refine ⟨222555980804230154895406397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148370653869486769930270931 222555980804230154895406397)
    ·
      refine ⟨83458492801586308085777399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222555980804230154895406397 83458492801586308085777399)
      ·
        refine ⟨125187739202379462128666099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83458492801586308085777399 125187739202379462128666099)
        ·
          refine ⟨187781608803569193192999149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125187739202379462128666099 187781608803569193192999149)
          ·
            refine ⟨70418103301338447447374681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187781608803569193192999149 70418103301338447447374681)
            ·
              refine ⟨52813577476003835585531011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70418103301338447447374681 52813577476003835585531011)
              ·
                refine ⟨79220366214005753378296517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52813577476003835585531011 79220366214005753378296517)
                ·
                  refine ⟨14853818665126078758430597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79220366214005753378296517 14853818665126078758430597)
                  ·
                    refine ⟨2785090999711139767205737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14853818665126078758430597 2785090999711139767205737)
                    ·
                      refine ⟨2088818249783354825404303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785090999711139767205737 2088818249783354825404303)
                      ·
                        rfl

theorem cell23_4067959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_4067959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067959 prefixEnd_4067959 := by exact prefixLift 4067959
  have htrace : WordTrace (prefixWord ++ tailWord_4067959) baseStart_4067959 baseEnd_4067959 := by
    simpa [prefixWord, tailWord_4067959, baseEnd_4067959] using wordTrace_append hprefix tailTrace_4067959
  have hstable : (prefixWord ++ tailWord_4067959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067959).length < 2 ^ (prefixWord ++ tailWord_4067959).sum := by decide
  have hdescent : baseEnd_4067959 < baseStart_4067959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4067996 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_4067996 : Nat := 118140960795 + 4067996 * 2 ^ 59
def prefixEnd_4067996 : Nat := 4983230072969 + 3 ^ 40 * 4067996 * 2
def baseEnd_4067996 : Nat := 2088837248567571180641633

theorem tailTrace_4067996 : CollatzResearch.WordTrace tailWord_4067996 prefixEnd_4067996 2088837248567571180641633 := by
  unfold tailWord_4067996
  simp only [CollatzResearch.WordTrace]
  refine ⟨74186001685176362624683921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98914668913568483499578561 74186001685176362624683921)
  ·
    refine ⟨55639501263882271968512941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74186001685176362624683921 55639501263882271968512941)
    ·
      refine ⟨20864812973955851988192353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55639501263882271968512941 20864812973955851988192353)
      ·
        refine ⟨15648609730466888991144265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20864812973955851988192353 15648609730466888991144265)
        ·
          refine ⟨11736457297850166743358199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15648609730466888991144265 11736457297850166743358199)
          ·
            refine ⟨17604685946775250115037299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11736457297850166743358199 17604685946775250115037299)
            ·
              refine ⟨26407028920162875172555949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17604685946775250115037299 26407028920162875172555949)
              ·
                refine ⟨9902635845061078189708481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26407028920162875172555949 9902635845061078189708481)
                ·
                  refine ⟨7426976883795808642281361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9902635845061078189708481 7426976883795808642281361)
                  ·
                    refine ⟨5570232662846856481711021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7426976883795808642281361 5570232662846856481711021)
                    ·
                      refine ⟨2088837248567571180641633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5570232662846856481711021 2088837248567571180641633)
                      ·
                        rfl

theorem cell23_4067996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_4067996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4067996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4067996 prefixEnd_4067996 := by exact prefixLift 4067996
  have htrace : WordTrace (prefixWord ++ tailWord_4067996) baseStart_4067996 baseEnd_4067996 := by
    simpa [prefixWord, tailWord_4067996, baseEnd_4067996] using wordTrace_append hprefix tailTrace_4067996
  have hstable : (prefixWord ++ tailWord_4067996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4067996).length < 2 ^ (prefixWord ++ tailWord_4067996).sum := by decide
  have hdescent : baseEnd_4067996 < baseStart_4067996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4067996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068026 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3]
def baseStart_4068026 : Nat := 118140960795 + 4068026 * 2 ^ 59
def prefixEnd_4068026 : Nat := 4983230072969 + 3 ^ 40 * 4068026 * 2
def baseEnd_4068026 : Nat := 2088852652987206063266495

theorem tailTrace_4068026 : CollatzResearch.WordTrace tailWord_4068026 prefixEnd_4068026 2088852652987206063266495 := by
  unfold tailWord_4068026
  simp only [CollatzResearch.WordTrace]
  refine ⟨37093274390061010093239983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98915398373496026915306621 37093274390061010093239983)
  ·
    refine ⟨55639911585091515139859975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37093274390061010093239983 55639911585091515139859975)
    ·
      refine ⟨83459867377637272709789963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55639911585091515139859975 83459867377637272709789963)
      ·
        refine ⟨125189801066455909064684945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83459867377637272709789963 125189801066455909064684945)
        ·
          refine ⟨93892350799841931798513709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125189801066455909064684945 93892350799841931798513709)
          ·
            refine ⟨35209631549940724424442641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93892350799841931798513709 35209631549940724424442641)
            ·
              refine ⟨26407223662455543318331981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35209631549940724424442641 26407223662455543318331981)
              ·
                refine ⟨9902708873420828744374493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26407223662455543318331981 9902708873420828744374493)
                ·
                  refine ⟨3713515827532810779140435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9902708873420828744374493 3713515827532810779140435)
                  ·
                    refine ⟨5570273741299216168710653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3713515827532810779140435 5570273741299216168710653)
                    ·
                      refine ⟨2088852652987206063266495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5570273741299216168710653 2088852652987206063266495)
                      ·
                        rfl

theorem cell23_4068026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_4068026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068026 prefixEnd_4068026 := by exact prefixLift 4068026
  have htrace : WordTrace (prefixWord ++ tailWord_4068026) baseStart_4068026 baseEnd_4068026 := by
    simpa [prefixWord, tailWord_4068026, baseEnd_4068026] using wordTrace_append hprefix tailTrace_4068026
  have hstable : (prefixWord ++ tailWord_4068026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068026).length < 2 ^ (prefixWord ++ tailWord_4068026).sum := by decide
  have hdescent : baseEnd_4068026 < baseStart_4068026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068029 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_4068029 : Nat := 118140960795 + 4068029 * 2 ^ 59
def prefixEnd_4068029 : Nat := 4983230072969 + 3 ^ 40 * 4068029 * 2
def baseEnd_4068029 : Nat := 696284731143056517176327

theorem tailTrace_4068029 : CollatzResearch.WordTrace tailWord_4068029 prefixEnd_4068029 696284731143056517176327 := by
  unfold tailWord_4068029
  simp only [CollatzResearch.WordTrace]
  refine ⟨148373206979233171885319141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98915471319488781256879427 148373206979233171885319141)
  ·
    refine ⟨27819976308606219728497339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148373206979233171885319141 27819976308606219728497339)
    ·
      refine ⟨41729964462909329592746009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27819976308606219728497339 41729964462909329592746009)
      ·
        refine ⟨31297473347181997194559507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41729964462909329592746009 31297473347181997194559507)
        ·
          refine ⟨46946210020772995791839261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31297473347181997194559507 46946210020772995791839261)
          ·
            refine ⟨17604828757789873421939723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46946210020772995791839261 17604828757789873421939723)
            ·
              refine ⟨26407243136684810132909585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17604828757789873421939723 26407243136684810132909585)
              ·
                refine ⟨19805432352513607599682189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26407243136684810132909585 19805432352513607599682189)
                ·
                  refine ⟨7427037132192602849880821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19805432352513607599682189 7427037132192602849880821)
                  ·
                    refine ⟨696284731143056517176327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7427037132192602849880821 696284731143056517176327)
                    ·
                      rfl

theorem cell23_4068029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_4068029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068029 prefixEnd_4068029 := by exact prefixLift 4068029
  have htrace : WordTrace (prefixWord ++ tailWord_4068029) baseStart_4068029 baseEnd_4068029 := by
    simpa [prefixWord, tailWord_4068029, baseEnd_4068029] using wordTrace_append hprefix tailTrace_4068029
  have hstable : (prefixWord ++ tailWord_4068029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068029).length < 2 ^ (prefixWord ++ tailWord_4068029).sum := by decide
  have hdescent : baseEnd_4068029 < baseStart_4068029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068049 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_4068049 : Nat := 118140960795 + 4068049 * 2 ^ 59
def prefixEnd_4068049 : Nat := 4983230072969 + 3 ^ 40 * 4068049 * 2
def baseEnd_4068049 : Nat := 2088864463042259473278889

theorem tailTrace_4068049 : CollatzResearch.WordTrace tailWord_4068049 prefixEnd_4068049 2088864463042259473278889 := by
  unfold tailWord_4068049
  simp only [CollatzResearch.WordTrace]
  refine ⟨148373936439160715301047201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98915957626107143534031467 148373936439160715301047201)
  ·
    refine ⟨111280452329370536475785401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148373936439160715301047201 111280452329370536475785401)
    ·
      refine ⟨83460339247027902356839051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111280452329370536475785401 83460339247027902356839051)
      ·
        refine ⟨125190508870541853535258577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83460339247027902356839051 125190508870541853535258577)
        ·
          refine ⟨93892881652906390151443933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125190508870541853535258577 93892881652906390151443933)
          ·
            refine ⟨35209830619839896306791475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93892881652906390151443933 35209830619839896306791475)
            ·
              refine ⟨52814745929759844460187213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35209830619839896306791475 52814745929759844460187213)
              ·
                refine ⟨19805529723659941672570205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52814745929759844460187213 19805529723659941672570205)
                ·
                  refine ⟨7427073646372478127213827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19805529723659941672570205 7427073646372478127213827)
                  ·
                    refine ⟨11140610469558717190820741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7427073646372478127213827 11140610469558717190820741)
                    ·
                      refine ⟨2088864463042259473278889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11140610469558717190820741 2088864463042259473278889)
                      ·
                        rfl

theorem cell23_4068049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_4068049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068049 prefixEnd_4068049 := by exact prefixLift 4068049
  have htrace : WordTrace (prefixWord ++ tailWord_4068049) baseStart_4068049 baseEnd_4068049 := by
    simpa [prefixWord, tailWord_4068049, baseEnd_4068049] using wordTrace_append hprefix tailTrace_4068049
  have hstable : (prefixWord ++ tailWord_4068049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068049).length < 2 ^ (prefixWord ++ tailWord_4068049).sum := by decide
  have hdescent : baseEnd_4068049 < baseStart_4068049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068063 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 1, 5]
def baseStart_4068063 : Nat := 118140960795 + 4068063 * 2 ^ 59
def prefixEnd_4068063 : Nat := 4983230072969 + 3 ^ 40 * 4068063 * 2
def baseEnd_4068063 : Nat := 696290550590474139501275

theorem tailTrace_4068063 : CollatzResearch.WordTrace tailWord_4068063 prefixEnd_4068063 696290550590474139501275 := by
  unfold tailWord_4068063
  simp only [CollatzResearch.WordTrace]
  refine ⟨148374447061109995692056843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98916298040739997128037895 148374447061109995692056843)
  ·
    refine ⟨222561670591664993538085265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148374447061109995692056843 222561670591664993538085265)
    ·
      refine ⟨166921252943748745153563949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222561670591664993538085265 166921252943748745153563949)
      ·
        refine ⟨62595469853905779432586481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166921252943748745153563949 62595469853905779432586481)
        ·
          refine ⟨46946602390429334574439861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62595469853905779432586481 46946602390429334574439861)
          ·
            refine ⟨4401243974102750116353737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46946602390429334574439861 4401243974102750116353737)
            ·
              refine ⟨3300932980577062587265303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4401243974102750116353737 3300932980577062587265303)
              ·
                refine ⟨4951399470865593880897955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300932980577062587265303 4951399470865593880897955)
                ·
                  refine ⟨7427099206298390821346933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951399470865593880897955 7427099206298390821346933)
                  ·
                    refine ⟨696290550590474139501275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7427099206298390821346933 696290550590474139501275)
                    ·
                      rfl

theorem cell23_4068063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 5].length) (baseStart_4068063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068063 prefixEnd_4068063 := by exact prefixLift 4068063
  have htrace : WordTrace (prefixWord ++ tailWord_4068063) baseStart_4068063 baseEnd_4068063 := by
    simpa [prefixWord, tailWord_4068063, baseEnd_4068063] using wordTrace_append hprefix tailTrace_4068063
  have hstable : (prefixWord ++ tailWord_4068063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068063).length < 2 ^ (prefixWord ++ tailWord_4068063).sum := by decide
  have hdescent : baseEnd_4068063 < baseStart_4068063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068086 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_4068086 : Nat := 118140960795 + 4068086 * 2 ^ 59
def prefixEnd_4068086 : Nat := 4983230072969 + 3 ^ 40 * 4068086 * 2
def baseEnd_4068086 : Nat := 2088883461826475828516219

theorem tailTrace_4068086 : CollatzResearch.WordTrace tailWord_4068086 prefixEnd_4068086 2088883461826475828516219 := by
  unfold tailWord_4068086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9273455371251666913759007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98916857293351113746762741 9273455371251666913759007)
  ·
    refine ⟨13910183056877500370638511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9273455371251666913759007 13910183056877500370638511)
    ·
      refine ⟨20865274585316250555957767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13910183056877500370638511 20865274585316250555957767)
      ·
        refine ⟨31297911877974375833936651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20865274585316250555957767 31297911877974375833936651)
        ·
          refine ⟨46946867816961563750904977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31297911877974375833936651 46946867816961563750904977)
          ·
            refine ⟨35210150862721172813178733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46946867816961563750904977 35210150862721172813178733)
            ·
              refine ⟨13203806573520439804942025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35210150862721172813178733 13203806573520439804942025)
              ·
                refine ⟨9902854930140329853706519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13203806573520439804942025 9902854930140329853706519)
                ·
                  refine ⟨14854282395210494780559779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9902854930140329853706519 14854282395210494780559779)
                  ·
                    refine ⟨22281423592815742170839669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14854282395210494780559779 22281423592815742170839669)
                    ·
                      refine ⟨2088883461826475828516219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22281423592815742170839669 2088883461826475828516219)
                      ·
                        rfl

theorem cell23_4068086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_4068086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068086 prefixEnd_4068086 := by exact prefixLift 4068086
  have htrace : WordTrace (prefixWord ++ tailWord_4068086) baseStart_4068086 baseEnd_4068086 := by
    simpa [prefixWord, tailWord_4068086, baseEnd_4068086] using wordTrace_append hprefix tailTrace_4068086
  have hstable : (prefixWord ++ tailWord_4068086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068086).length < 2 ^ (prefixWord ++ tailWord_4068086).sum := by decide
  have hdescent : baseEnd_4068086 < baseStart_4068086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068093 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_4068093 : Nat := 118140960795 + 4068093 * 2 ^ 59
def prefixEnd_4068093 : Nat := 4983230072969 + 3 ^ 40 * 4068093 * 2
def baseEnd_4068093 : Nat := 696295685397019100376229

theorem tailTrace_4068093 : CollatzResearch.WordTrace tailWord_4068093 prefixEnd_4068093 696295685397019100376229 := by
  unfold tailWord_4068093
  simp only [CollatzResearch.WordTrace]
  refine ⟨148375541251001310815648933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98917027500667540543765955 148375541251001310815648933)
  ·
    refine ⟨27820413984562745777934175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148375541251001310815648933 27820413984562745777934175)
    ·
      refine ⟨41730620976844118666901263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27820413984562745777934175 41730620976844118666901263)
      ·
        refine ⟨62595931465266178000351895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41730620976844118666901263 62595931465266178000351895)
        ·
          refine ⟨93893897197899267000527843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62595931465266178000351895 93893897197899267000527843)
          ·
            refine ⟨140840845796848900500791765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93893897197899267000527843 140840845796848900500791765)
            ·
              refine ⟨3300957323363646105487307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 140840845796848900500791765 3300957323363646105487307)
              ·
                refine ⟨4951435985045469158230961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300957323363646105487307 4951435985045469158230961)
                ·
                  refine ⟨3713576988784101868673221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4951435985045469158230961 3713576988784101868673221)
                  ·
                    refine ⟨696295685397019100376229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3713576988784101868673221 696295685397019100376229)
                    ·
                      rfl

theorem cell23_4068093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_4068093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068093 prefixEnd_4068093 := by exact prefixLift 4068093
  have htrace : WordTrace (prefixWord ++ tailWord_4068093) baseStart_4068093 baseEnd_4068093 := by
    simpa [prefixWord, tailWord_4068093, baseEnd_4068093] using wordTrace_append hprefix tailTrace_4068093
  have hstable : (prefixWord ++ tailWord_4068093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068093).length < 2 ^ (prefixWord ++ tailWord_4068093).sum := by decide
  have hdescent : baseEnd_4068093 < baseStart_4068093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068103 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4068103 : Nat := 118140960795 + 4068103 * 2 ^ 59
def prefixEnd_4068103 : Nat := 4983230072969 + 3 ^ 40 * 4068103 * 2
def baseEnd_4068103 : Nat := 2088892190997602262003641

theorem tailTrace_4068103 : CollatzResearch.WordTrace tailWord_4068103 prefixEnd_4068103 2088892190997602262003641 := by
  unfold tailWord_4068103
  simp only [CollatzResearch.WordTrace]
  refine ⟨148375905980965082523512963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98917270653976721682341975 148375905980965082523512963)
  ·
    refine ⟨222563858971447623785269445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148375905980965082523512963 222563858971447623785269445)
    ·
      refine ⟨41730723557146429459738021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222563858971447623785269445 41730723557146429459738021)
      ·
        refine ⟨7824510666964955523700879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41730723557146429459738021 7824510666964955523700879)
        ·
          refine ⟨11736766000447433285551319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7824510666964955523700879 11736766000447433285551319)
          ·
            refine ⟨17605149000671149928326979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11736766000447433285551319 17605149000671149928326979)
            ·
              refine ⟨26407723501006724892490469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17605149000671149928326979 26407723501006724892490469)
              ·
                refine ⟨4951448156438760917341963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26407723501006724892490469 4951448156438760917341963)
                ·
                  refine ⟨7427172234658141376012945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951448156438760917341963 7427172234658141376012945)
                  ·
                    refine ⟨5570379175993606032009709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7427172234658141376012945 5570379175993606032009709)
                    ·
                      refine ⟨2088892190997602262003641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5570379175993606032009709 2088892190997602262003641)
                      ·
                        rfl

theorem cell23_4068103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4068103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068103 prefixEnd_4068103 := by exact prefixLift 4068103
  have htrace : WordTrace (prefixWord ++ tailWord_4068103) baseStart_4068103 baseEnd_4068103 := by
    simpa [prefixWord, tailWord_4068103, baseEnd_4068103] using wordTrace_append hprefix tailTrace_4068103
  have hstable : (prefixWord ++ tailWord_4068103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068103).length < 2 ^ (prefixWord ++ tailWord_4068103).sum := by decide
  have hdescent : baseEnd_4068103 < baseStart_4068103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068129 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4068129 : Nat := 118140960795 + 4068129 * 2 ^ 59
def prefixEnd_4068129 : Nat := 4983230072969 + 3 ^ 40 * 4068129 * 2
def baseEnd_4068129 : Nat := 2088905541494619160278521

theorem tailTrace_4068129 : CollatzResearch.WordTrace tailWord_4068129 prefixEnd_4068129 2088905541494619160278521 := by
  unfold tailWord_4068129
  simp only [CollatzResearch.WordTrace]
  refine ⟨148376854278870888963959441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98917902852580592642639627 148376854278870888963959441)
  ·
    refine ⟨111282640709153166722969581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148376854278870888963959441 111282640709153166722969581)
    ·
      refine ⟨41730990265932437521113593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111282640709153166722969581 41730990265932437521113593)
      ·
        refine ⟨31298242699449328140835195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41730990265932437521113593 31298242699449328140835195)
        ·
          refine ⟨46947364049173992211252793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31298242699449328140835195 46947364049173992211252793)
          ·
            refine ⟨35210523036880494158439595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46947364049173992211252793 35210523036880494158439595)
            ·
              refine ⟨52815784555320741237659393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35210523036880494158439595 52815784555320741237659393)
              ·
                refine ⟨39611838416490555928244545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52815784555320741237659393 39611838416490555928244545)
                ·
                  refine ⟨29708878812367916946183409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39611838416490555928244545 29708878812367916946183409)
                  ·
                    refine ⟨22281659109275937709637557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29708878812367916946183409 22281659109275937709637557)
                    ·
                      refine ⟨2088905541494619160278521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22281659109275937709637557 2088905541494619160278521)
                      ·
                        rfl

theorem cell23_4068129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4068129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068129 prefixEnd_4068129 := by exact prefixLift 4068129
  have htrace : WordTrace (prefixWord ++ tailWord_4068129) baseStart_4068129 baseEnd_4068129 := by
    simpa [prefixWord, tailWord_4068129, baseEnd_4068129] using wordTrace_append hprefix tailTrace_4068129
  have hstable : (prefixWord ++ tailWord_4068129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068129).length < 2 ^ (prefixWord ++ tailWord_4068129).sum := by decide
  have hdescent : baseEnd_4068129 < baseStart_4068129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068133 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 3]
def baseStart_4068133 : Nat := 118140960795 + 4068133 * 2 ^ 59
def prefixEnd_4068133 : Nat := 4983230072969 + 3 ^ 40 * 4068133 * 2
def baseEnd_4068133 : Nat := 2088907595417237144628503

theorem tailTrace_4068133 : CollatzResearch.WordTrace tailWord_4068133 prefixEnd_4068133 2088907595417237144628503 := by
  unfold tailWord_4068133
  simp only [CollatzResearch.WordTrace]
  refine ⟨148377000170856397647105053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98918000113904265098070035 148377000170856397647105053)
  ·
    refine ⟨55641375064071149117664395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148377000170856397647105053 55641375064071149117664395)
    ·
      refine ⟨83462062596106723676496593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55641375064071149117664395 83462062596106723676496593)
      ·
        refine ⟨62596546947080042757372445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83462062596106723676496593 62596546947080042757372445)
        ·
          refine ⟨23473705105155016034014667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62596546947080042757372445 23473705105155016034014667)
          ·
            refine ⟨35210557657732524051022001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23473705105155016034014667 35210557657732524051022001)
            ·
              refine ⟨26407918243299393038266501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35210557657732524051022001 26407918243299393038266501)
              ·
                refine ⟨4951484670618636194674969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26407918243299393038266501 4951484670618636194674969)
                ·
                  refine ⟨3713613502963977146006227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4951484670618636194674969 3713613502963977146006227)
                  ·
                    refine ⟨5570420254445965719009341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3713613502963977146006227 5570420254445965719009341)
                    ·
                      refine ⟨2088907595417237144628503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5570420254445965719009341 2088907595417237144628503)
                      ·
                        rfl

theorem cell23_4068133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_4068133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068133 prefixEnd_4068133 := by exact prefixLift 4068133
  have htrace : WordTrace (prefixWord ++ tailWord_4068133) baseStart_4068133 baseEnd_4068133 := by
    simpa [prefixWord, tailWord_4068133, baseEnd_4068133] using wordTrace_append hprefix tailTrace_4068133
  have hstable : (prefixWord ++ tailWord_4068133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068133).length < 2 ^ (prefixWord ++ tailWord_4068133).sum := by decide
  have hdescent : baseEnd_4068133 < baseStart_4068133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068177 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 1, 3, 2]
def baseStart_4068177 : Nat := 118140960795 + 4068177 * 2 ^ 59
def prefixEnd_4068177 : Nat := 4983230072969 + 3 ^ 40 * 4068177 * 2
def baseEnd_4068177 : Nat := 2088930188566034972478301

theorem tailTrace_4068177 : CollatzResearch.WordTrace tailWord_4068177 prefixEnd_4068177 2088930188566034972478301 := by
  unfold tailWord_4068177
  simp only [CollatzResearch.WordTrace]
  refine ⟨148378604982696993161706785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98919069988464662107804523 148378604982696993161706785)
  ·
    refine ⟨111283953737022744871280089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148378604982696993161706785 111283953737022744871280089)
    ·
      refine ⟨83462965302767058653460067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111283953737022744871280089 83462965302767058653460067)
      ·
        refine ⟨125194447954150587980190101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83462965302767058653460067 125194447954150587980190101)
        ·
          refine ⟨5868489747850808811571411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125194447954150587980190101 5868489747850808811571411)
          ·
            refine ⟨8802734621776213217357117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5868489747850808811571411 8802734621776213217357117)
            ·
              refine ⟨3301025483166079956508919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8802734621776213217357117 3301025483166079956508919)
              ·
                refine ⟨4951538224749119934763379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3301025483166079956508919 4951538224749119934763379)
                ·
                  refine ⟨7427307337123679902145069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4951538224749119934763379 7427307337123679902145069)
                  ·
                    refine ⟨2785240251421379963304401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7427307337123679902145069 2785240251421379963304401)
                    ·
                      refine ⟨2088930188566034972478301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2785240251421379963304401 2088930188566034972478301)
                      ·
                        rfl

theorem cell23_4068177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_4068177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068177 prefixEnd_4068177 := by exact prefixLift 4068177
  have htrace : WordTrace (prefixWord ++ tailWord_4068177) baseStart_4068177 baseEnd_4068177 := by
    simpa [prefixWord, tailWord_4068177, baseEnd_4068177] using wordTrace_append hprefix tailTrace_4068177
  have hstable : (prefixWord ++ tailWord_4068177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068177).length < 2 ^ (prefixWord ++ tailWord_4068177).sum := by decide
  have hdescent : baseEnd_4068177 < baseStart_4068177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068219 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 7]
def baseStart_4068219 : Nat := 118140960795 + 4068219 * 2 ^ 59
def prefixEnd_4068219 : Nat := 4983230072969 + 3 ^ 40 * 4068219 * 2
def baseEnd_4068219 : Nat := 2088951754753523808153107

theorem tailTrace_4068219 : CollatzResearch.WordTrace tailWord_4068219 prefixEnd_4068219 2088951754753523808153107 := by
  unfold tailWord_4068219
  simp only [CollatzResearch.WordTrace]
  refine ⟨148380136848544834334735711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98920091232363222889823807 148380136848544834334735711)
  ·
    refine ⟨222570205272817251502103567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148380136848544834334735711 222570205272817251502103567)
    ·
      refine ⟨333855307909225877253155351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222570205272817251502103567 333855307909225877253155351)
      ·
        refine ⟨500782961863838815879733027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333855307909225877253155351 500782961863838815879733027)
        ·
          refine ⟨751174442795758223819599541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500782961863838815879733027 751174442795758223819599541)
          ·
            refine ⟨70422604012102333483087457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 751174442795758223819599541 70422604012102333483087457)
            ·
              refine ⟨52816953009076750112315593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70422604012102333483087457 52816953009076750112315593)
              ·
                refine ⟨39612714756807562584236695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52816953009076750112315593 39612714756807562584236695)
                ·
                  refine ⟨59419072135211343876355043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39612714756807562584236695 59419072135211343876355043)
                  ·
                    refine ⟨89128608202817015814532565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59419072135211343876355043 89128608202817015814532565)
                    ·
                      refine ⟨2088951754753523808153107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89128608202817015814532565 2088951754753523808153107)
                      ·
                        rfl

theorem cell23_4068219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_4068219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068219 prefixEnd_4068219 := by exact prefixLift 4068219
  have htrace : WordTrace (prefixWord ++ tailWord_4068219) baseStart_4068219 baseEnd_4068219 := by
    simpa [prefixWord, tailWord_4068219, baseEnd_4068219] using wordTrace_append hprefix tailTrace_4068219
  have hstable : (prefixWord ++ tailWord_4068219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068219).length < 2 ^ (prefixWord ++ tailWord_4068219).sum := by decide
  have hdescent : baseEnd_4068219 < baseStart_4068219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4068286 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_4068286 : Nat := 118140960795 + 4068286 * 2 ^ 59
def prefixEnd_4068286 : Nat := 4983230072969 + 3 ^ 40 * 4068286 * 2
def baseEnd_4068286 : Nat := 232109573106375005112811

theorem tailTrace_4068286 : CollatzResearch.WordTrace tailWord_4068286 prefixEnd_4068286 232109573106375005112811 := by
  unfold tailWord_4068286
  simp only [CollatzResearch.WordTrace]
  refine ⟨18547822567412763097178089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98921720359534736518283141 18547822567412763097178089)
  ·
    refine ⟨13910866925559572322883567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18547822567412763097178089 13910866925559572322883567)
    ·
      refine ⟨20866300388339358484325351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13910866925559572322883567 20866300388339358484325351)
      ·
        refine ⟨31299450582509037726488027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20866300388339358484325351 31299450582509037726488027)
        ·
          refine ⟨46949175873763556589732041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31299450582509037726488027 46949175873763556589732041)
          ·
            refine ⟨35211881905322667442299031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46949175873763556589732041 35211881905322667442299031)
            ·
              refine ⟨52817822857984001163448547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35211881905322667442299031 52817822857984001163448547)
              ·
                refine ⟨79226734286976001745172821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52817822857984001163448547 79226734286976001745172821)
                ·
                  refine ⟨232109573106375005112811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 79226734286976001745172821 232109573106375005112811)
                  ·
                    rfl

theorem cell23_4068286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_4068286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4068286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4068286 prefixEnd_4068286 := by exact prefixLift 4068286
  have htrace : WordTrace (prefixWord ++ tailWord_4068286) baseStart_4068286 baseEnd_4068286 := by
    simpa [prefixWord, tailWord_4068286, baseEnd_4068286] using wordTrace_append hprefix tailTrace_4068286
  have hstable : (prefixWord ++ tailWord_4068286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4068286).length < 2 ^ (prefixWord ++ tailWord_4068286).sum := by decide
  have hdescent : baseEnd_4068286 < baseStart_4068286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4068286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
