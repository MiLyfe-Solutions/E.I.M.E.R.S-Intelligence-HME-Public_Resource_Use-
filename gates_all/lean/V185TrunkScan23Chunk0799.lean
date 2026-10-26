import V185TrunkScan23Chunk0798

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4725720 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 9]
def baseStart_4725720 : Nat := 118140960795 + 4725720 * 2 ^ 59
def prefixEnd_4725720 : Nat := 4983230072969 + 3 ^ 40 * 4725720 * 2
def baseEnd_4725720 : Nat := 269618422062817314718535

theorem tailTrace_4725720 : CollatzResearch.WordTrace tailWord_4725720 prefixEnd_4725720 269618422062817314718535 := by
  unfold tailWord_4725720
  simp only [CollatzResearch.WordTrace]
  refine ⟨86180584219765501782747307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114907445626354002376996409 86180584219765501782747307)
  ·
    refine ⟨129270876329648252674120961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86180584219765501782747307 129270876329648252674120961)
    ·
      refine ⟨96953157247236189505590721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129270876329648252674120961 96953157247236189505590721)
      ·
        refine ⟨72714867935427142129193041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96953157247236189505590721 72714867935427142129193041)
        ·
          refine ⟨54536150951570356596894781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72714867935427142129193041 54536150951570356596894781)
          ·
            refine ⟨20451056606838883723835543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54536150951570356596894781 20451056606838883723835543)
            ·
              refine ⟨30676584910258325585753315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20451056606838883723835543 30676584910258325585753315)
              ·
                refine ⟨46014877365387488378629973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30676584910258325585753315 46014877365387488378629973)
                ·
                  refine ⟨269618422062817314718535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46014877365387488378629973 269618422062817314718535)
                  ·
                    rfl

theorem cell23_4725720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 9].length) (baseStart_4725720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725720 prefixEnd_4725720 := by exact prefixLift 4725720
  have htrace : WordTrace (prefixWord ++ tailWord_4725720) baseStart_4725720 baseEnd_4725720 := by
    simpa [prefixWord, tailWord_4725720, baseEnd_4725720] using wordTrace_append hprefix tailTrace_4725720
  have hstable : (prefixWord ++ tailWord_4725720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725720).length < 2 ^ (prefixWord ++ tailWord_4725720).sum := by decide
  have hdescent : baseEnd_4725720 < baseStart_4725720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725760 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_4725760 : Nat := 118140960795 + 4725760 * 2 ^ 59
def prefixEnd_4725760 : Nat := 4983230072969 + 3 ^ 40 * 4725760 * 2
def baseEnd_4725760 : Nat := 2426586337791535675966631

theorem tailTrace_4725760 : CollatzResearch.WordTrace tailWord_4725760 prefixEnd_4725760 2426586337791535675966631 := by
  unfold tailWord_4725760
  simp only [CollatzResearch.WordTrace]
  refine ⟨86181313679693045198475367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114908418239590726931300489 86181313679693045198475367)
  ·
    refine ⟨129271970519539567797713051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86181313679693045198475367 129271970519539567797713051)
    ·
      refine ⟨193907955779309351696569577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129271970519539567797713051 193907955779309351696569577)
      ·
        refine ⟨145430966834482013772427183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193907955779309351696569577 145430966834482013772427183)
        ·
          refine ⟨218146450251723020658640775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145430966834482013772427183 218146450251723020658640775)
          ·
            refine ⟨327219675377584530987961163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218146450251723020658640775 327219675377584530987961163)
            ·
              refine ⟨490829513066376796481941745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327219675377584530987961163 490829513066376796481941745)
              ·
                refine ⟨368122134799782597361456309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490829513066376796481941745 368122134799782597361456309)
                ·
                  refine ⟨34511450137479618502636529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 368122134799782597361456309 34511450137479618502636529)
                  ·
                    refine ⟨25883587603109713876977397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34511450137479618502636529 25883587603109713876977397)
                    ·
                      refine ⟨2426586337791535675966631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25883587603109713876977397 2426586337791535675966631)
                      ·
                        rfl

theorem cell23_4725760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_4725760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725760 prefixEnd_4725760 := by exact prefixLift 4725760
  have htrace : WordTrace (prefixWord ++ tailWord_4725760) baseStart_4725760 baseEnd_4725760 := by
    simpa [prefixWord, tailWord_4725760, baseEnd_4725760] using wordTrace_append hprefix tailTrace_4725760
  have hstable : (prefixWord ++ tailWord_4725760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725760).length < 2 ^ (prefixWord ++ tailWord_4725760).sum := by decide
  have hdescent : baseEnd_4725760 < baseStart_4725760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725788 : List Nat := [2, 2, 3, 1, 5, 1, 1, 3, 5]
def baseStart_4725788 : Nat := 118140960795 + 4725788 * 2 ^ 59
def prefixEnd_4725788 : Nat := 4983230072969 + 3 ^ 40 * 4725788 * 2
def baseEnd_4725788 : Nat := 269622301694429062935167

theorem tailTrace_4725788 : CollatzResearch.WordTrace tailWord_4725788 prefixEnd_4725788 269622301694429062935167 := by
  unfold tailWord_4725788
  simp only [CollatzResearch.WordTrace]
  refine ⟨86181824301642325589485009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114909099068856434119313345 86181824301642325589485009)
  ·
    refine ⟨64636368226231744192113757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86181824301642325589485009 64636368226231744192113757)
    ·
      refine ⟨24238638084836904072042659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64636368226231744192113757 24238638084836904072042659)
      ·
        refine ⟨36357957127255356108063989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24238638084836904072042659 36357957127255356108063989)
        ·
          refine ⟨3408558480680189635130999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36357957127255356108063989 3408558480680189635130999)
          ·
            refine ⟨5112837721020284452696499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408558480680189635130999 5112837721020284452696499)
            ·
              refine ⟨7669256581530426679044749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112837721020284452696499 7669256581530426679044749)
              ·
                refine ⟨2875971218073910004641781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7669256581530426679044749 2875971218073910004641781)
                ·
                  refine ⟨269622301694429062935167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2875971218073910004641781 269622301694429062935167)
                  ·
                    rfl

theorem cell23_4725788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_4725788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725788 prefixEnd_4725788 := by exact prefixLift 4725788
  have htrace : WordTrace (prefixWord ++ tailWord_4725788) baseStart_4725788 baseEnd_4725788 := by
    simpa [prefixWord, tailWord_4725788, baseEnd_4725788] using wordTrace_append hprefix tailTrace_4725788
  have hstable : (prefixWord ++ tailWord_4725788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725788).length < 2 ^ (prefixWord ++ tailWord_4725788).sum := by decide
  have hdescent : baseEnd_4725788 < baseStart_4725788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725827 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 6]
def baseStart_4725827 : Nat := 118140960795 + 4725827 * 2 ^ 59
def prefixEnd_4725827 : Nat := 4983230072969 + 3 ^ 40 * 4725827 * 2
def baseEnd_4725827 : Nat := 269624526777265212647647

theorem tailTrace_4725827 : CollatzResearch.WordTrace tailWord_4725827 prefixEnd_4725827 269624526777265212647647 := by
  unfold tailWord_4725827
  simp only [CollatzResearch.WordTrace]
  refine ⟨172365071050143360839639735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114910047366762240559759823 172365071050143360839639735)
  ·
    refine ⟨258547606575215041259459603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172365071050143360839639735 258547606575215041259459603)
    ·
      refine ⟨387821409862822561889189405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258547606575215041259459603 387821409862822561889189405)
      ·
        refine ⟨145433028698558460708446027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 387821409862822561889189405 145433028698558460708446027)
        ·
          refine ⟨218149543047837691062669041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145433028698558460708446027 218149543047837691062669041)
          ·
            refine ⟨163612157285878268297001781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218149543047837691062669041 163612157285878268297001781)
            ·
              refine ⟨15338639745551087652843917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163612157285878268297001781 15338639745551087652843917)
              ·
                refine ⟨5751989904581657869816469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15338639745551087652843917 5751989904581657869816469)
                ·
                  refine ⟨269624526777265212647647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5751989904581657869816469 269624526777265212647647)
                  ·
                    rfl

theorem cell23_4725827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 6].length) (baseStart_4725827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725827 prefixEnd_4725827 := by exact prefixLift 4725827
  have htrace : WordTrace (prefixWord ++ tailWord_4725827) baseStart_4725827 baseEnd_4725827 := by
    simpa [prefixWord, tailWord_4725827, baseEnd_4725827] using wordTrace_append hprefix tailTrace_4725827
  have hstable : (prefixWord ++ tailWord_4725827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725827).length < 2 ^ (prefixWord ++ tailWord_4725827).sum := by decide
  have hdescent : baseEnd_4725827 < baseStart_4725827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725911 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 4]
def baseStart_4725911 : Nat := 118140960795 + 4725911 * 2 ^ 59
def prefixEnd_4725911 : Nat := 4983230072969 + 3 ^ 40 * 4725911 * 2
def baseEnd_4725911 : Nat := 2426663873370364585178437

theorem tailTrace_4725911 : CollatzResearch.WordTrace tailWord_4725911 prefixEnd_4725911 2426663873370364585178437 := by
  unfold tailWord_4725911
  simp only [CollatzResearch.WordTrace]
  refine ⟨172368134781839043185697587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114912089854559362123798391 172368134781839043185697587)
  ·
    refine ⟨258552202172758564778546381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172368134781839043185697587 258552202172758564778546381)
    ·
      refine ⟨96957075814784461791954893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258552202172758564778546381 96957075814784461791954893)
      ·
        refine ⟨36358903430544173171983085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96957075814784461791954893 36358903430544173171983085)
        ·
          refine ⟨13634588786454064939493657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36358903430544173171983085 13634588786454064939493657)
          ·
            refine ⟨10225941589840548704620243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13634588786454064939493657 10225941589840548704620243)
            ·
              refine ⟨15338912384760823056930365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10225941589840548704620243 15338912384760823056930365)
              ·
                refine ⟨5752092144285308646348887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15338912384760823056930365 5752092144285308646348887)
                ·
                  refine ⟨8628138216427962969523331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5752092144285308646348887 8628138216427962969523331)
                  ·
                    refine ⟨12942207324641944454284997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8628138216427962969523331 12942207324641944454284997)
                    ·
                      refine ⟨2426663873370364585178437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12942207324641944454284997 2426663873370364585178437)
                      ·
                        rfl

theorem cell23_4725911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_4725911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725911 prefixEnd_4725911 := by exact prefixLift 4725911
  have htrace : WordTrace (prefixWord ++ tailWord_4725911) baseStart_4725911 baseEnd_4725911 := by
    simpa [prefixWord, tailWord_4725911, baseEnd_4725911] using wordTrace_append hprefix tailTrace_4725911
  have hstable : (prefixWord ++ tailWord_4725911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725911).length < 2 ^ (prefixWord ++ tailWord_4725911).sum := by decide
  have hdescent : baseEnd_4725911 < baseStart_4725911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725917 : List Nat := [1, 4, 2, 1, 1, 2, 12]
def baseStart_4725917 : Nat := 118140960795 + 4725917 * 2 ^ 59
def prefixEnd_4725917 : Nat := 4983230072969 + 3 ^ 40 * 4725917 * 2
def baseEnd_4725917 : Nat := 29958851287090019280289

theorem tailTrace_4725917 : CollatzResearch.WordTrace tailWord_4725917 prefixEnd_4725917 29958851287090019280289 := by
  unfold tailWord_4725917
  simp only [CollatzResearch.WordTrace]
  refine ⟨172368353619817306210416005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114912235746544870806944003 172368353619817306210416005)
  ·
    refine ⟨32319066303715744914453001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172368353619817306210416005 32319066303715744914453001)
    ·
      refine ⟨24239299727786808685839751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32319066303715744914453001 24239299727786808685839751)
      ·
        refine ⟨36358949591680213028759627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24239299727786808685839751 36358949591680213028759627)
        ·
          refine ⟨54538424387520319543139441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36358949591680213028759627 54538424387520319543139441)
          ·
            refine ⟨40903818290640239657354581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54538424387520319543139441 40903818290640239657354581)
            ·
              refine ⟨29958851287090019280289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 40903818290640239657354581 29958851287090019280289)
              ·
                rfl

theorem cell23_4725917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 12].length) (baseStart_4725917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725917 prefixEnd_4725917 := by exact prefixLift 4725917
  have htrace : WordTrace (prefixWord ++ tailWord_4725917) baseStart_4725917 baseEnd_4725917 := by
    simpa [prefixWord, tailWord_4725917, baseEnd_4725917] using wordTrace_append hprefix tailTrace_4725917
  have hstable : (prefixWord ++ tailWord_4725917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725917).length < 2 ^ (prefixWord ++ tailWord_4725917).sum := by decide
  have hdescent : baseEnd_4725917 < baseStart_4725917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725938 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_4725938 : Nat := 118140960795 + 4725938 * 2 ^ 59
def prefixEnd_4725938 : Nat := 4983230072969 + 3 ^ 40 * 4725938 * 2
def baseEnd_4725938 : Nat := 808892579116011993180271

theorem tailTrace_4725938 : CollatzResearch.WordTrace tailWord_4725938 prefixEnd_4725938 808892579116011993180271 := by
  unfold tailWord_4725938
  simp only [CollatzResearch.WordTrace]
  refine ⟨43092279888185306699232617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114912746368494151197953645 43092279888185306699232617)
  ·
    refine ⟨32319209916138980024424463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43092279888185306699232617 32319209916138980024424463)
    ·
      refine ⟨48478814874208470036636695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32319209916138980024424463 48478814874208470036636695)
      ·
        refine ⟨72718222311312705054955043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48478814874208470036636695 72718222311312705054955043)
        ·
          refine ⟨109077333466969057582432565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72718222311312705054955043 109077333466969057582432565)
          ·
            refine ⟨10226000012528349148353053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109077333466969057582432565 10226000012528349148353053)
            ·
              refine ⟨3834750004698130930632395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10226000012528349148353053 3834750004698130930632395)
              ·
                refine ⟨5752125007047196395948593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834750004698130930632395 5752125007047196395948593)
                ·
                  refine ⟨4314093755285397296961445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5752125007047196395948593 4314093755285397296961445)
                  ·
                    refine ⟨808892579116011993180271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4314093755285397296961445 808892579116011993180271)
                    ·
                      rfl

theorem cell23_4725938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_4725938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725938 prefixEnd_4725938 := by exact prefixLift 4725938
  have htrace : WordTrace (prefixWord ++ tailWord_4725938) baseStart_4725938 baseEnd_4725938 := by
    simpa [prefixWord, tailWord_4725938, baseEnd_4725938] using wordTrace_append hprefix tailTrace_4725938
  have hstable : (prefixWord ++ tailWord_4725938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725938).length < 2 ^ (prefixWord ++ tailWord_4725938).sum := by decide
  have hdescent : baseEnd_4725938 < baseStart_4725938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725944 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_4725944 : Nat := 118140960795 + 4725944 * 2 ^ 59
def prefixEnd_4725944 : Nat := 4983230072969 + 3 ^ 40 * 4725944 * 2
def baseEnd_4725944 : Nat := 2426680818231962956065785

theorem tailTrace_4725944 : CollatzResearch.WordTrace tailWord_4725944 prefixEnd_4725944 2426680818231962956065785 := by
  unfold tailWord_4725944
  simp only [CollatzResearch.WordTrace]
  refine ⟨86184669195359744910824443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114912892260479659881099257 86184669195359744910824443)
  ·
    refine ⟨129277003793039617366236665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86184669195359744910824443 129277003793039617366236665)
    ·
      refine ⟨96957752844779713024677499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129277003793039617366236665 96957752844779713024677499)
      ·
        refine ⟨145436629267169569537016249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96957752844779713024677499 145436629267169569537016249)
        ·
          refine ⟨109077471950377177152762187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145436629267169569537016249 109077471950377177152762187)
          ·
            refine ⟨163616207925565765729143281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109077471950377177152762187 163616207925565765729143281)
            ·
              refine ⟨122712155944174324296857461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163616207925565765729143281 122712155944174324296857461)
              ·
                refine ⟨11504264619766342902830387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122712155944174324296857461 11504264619766342902830387)
                ·
                  refine ⟨17256396929649514354245581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11504264619766342902830387 17256396929649514354245581)
                  ·
                    refine ⟨6471148848618567882842093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17256396929649514354245581 6471148848618567882842093)
                    ·
                      refine ⟨2426680818231962956065785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6471148848618567882842093 2426680818231962956065785)
                      ·
                        rfl

theorem cell23_4725944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_4725944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725944 prefixEnd_4725944 := by exact prefixLift 4725944
  have htrace : WordTrace (prefixWord ++ tailWord_4725944) baseStart_4725944 baseEnd_4725944 := by
    simpa [prefixWord, tailWord_4725944, baseEnd_4725944] using wordTrace_append hprefix tailTrace_4725944
  have hstable : (prefixWord ++ tailWord_4725944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725944).length < 2 ^ (prefixWord ++ tailWord_4725944).sum := by decide
  have hdescent : baseEnd_4725944 < baseStart_4725944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725948 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 1, 2, 3]
def baseStart_4725948 : Nat := 118140960795 + 4725948 * 2 ^ 59
def prefixEnd_4725948 : Nat := 4983230072969 + 3 ^ 40 * 4725948 * 2
def baseEnd_4725948 : Nat := 2426682872154580940415767

theorem tailTrace_4725948 : CollatzResearch.WordTrace tailWord_4725948 prefixEnd_4725948 2426682872154580940415767 := by
  unfold tailWord_4725948
  simp only [CollatzResearch.WordTrace]
  refine ⟨86184742141352499252397249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114912989521803332336529665 86184742141352499252397249)
  ·
    refine ⟨64638556606014374439297937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86184742141352499252397249 64638556606014374439297937)
    ·
      refine ⟨48478917454510780829473453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64638556606014374439297937 48478917454510780829473453)
      ·
        refine ⟨18179594045441542811052545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48478917454510780829473453 18179594045441542811052545)
        ·
          refine ⟨13634695534081157108289409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18179594045441542811052545 13634695534081157108289409)
          ·
            refine ⟨10226021650560867831217057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13634695534081157108289409 10226021650560867831217057)
            ·
              refine ⟨7669516237920650873412793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10226021650560867831217057 7669516237920650873412793)
              ·
                refine ⟨5752137178440488155059595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7669516237920650873412793 5752137178440488155059595)
                ·
                  refine ⟨8628205767660732232589393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5752137178440488155059595 8628205767660732232589393)
                  ·
                    refine ⟨6471154325745549174442045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8628205767660732232589393 6471154325745549174442045)
                    ·
                      refine ⟨2426682872154580940415767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6471154325745549174442045 2426682872154580940415767)
                      ·
                        rfl

theorem cell23_4725948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_4725948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725948 prefixEnd_4725948 := by exact prefixLift 4725948
  have htrace : WordTrace (prefixWord ++ tailWord_4725948) baseStart_4725948 baseEnd_4725948 := by
    simpa [prefixWord, tailWord_4725948, baseEnd_4725948] using wordTrace_append hprefix tailTrace_4725948
  have hstable : (prefixWord ++ tailWord_4725948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725948).length < 2 ^ (prefixWord ++ tailWord_4725948).sum := by decide
  have hdescent : baseEnd_4725948 < baseStart_4725948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725962 : List Nat := [3, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2]
def baseStart_4725962 : Nat := 118140960795 + 4725962 * 2 ^ 59
def prefixEnd_4725962 : Nat := 4983230072969 + 3 ^ 40 * 4725962 * 2
def baseEnd_4725962 : Nat := 2426690060883743885640703

theorem tailTrace_4725962 : CollatzResearch.WordTrace tailWord_4725962 prefixEnd_4725962 2426690060883743885640703 := by
  unfold tailWord_4725962
  simp only [CollatzResearch.WordTrace]
  refine ⟨43092498726163569723951035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114913329936436185930536093 43092498726163569723951035)
  ·
    refine ⟨64638748089245354585926553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43092498726163569723951035 64638748089245354585926553)
    ·
      refine ⟨48479061066934015939444915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64638748089245354585926553 48479061066934015939444915)
      ·
        refine ⟨72718591600401023909167373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48479061066934015939444915 72718591600401023909167373)
        ·
          refine ⟨27269471850150383965937765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72718591600401023909167373 27269471850150383965937765)
          ·
            refine ⟨5113025971903196993613331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27269471850150383965937765 5113025971903196993613331)
            ·
              refine ⟨7669538957854795490419997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5113025971903196993613331 7669538957854795490419997)
              ·
                refine ⟨2876077109195548308907499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7669538957854795490419997 2876077109195548308907499)
                ·
                  refine ⟨4314115663793322463361249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876077109195548308907499 4314115663793322463361249)
                  ·
                    refine ⟨3235586747844991847520937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4314115663793322463361249 3235586747844991847520937)
                    ·
                      refine ⟨2426690060883743885640703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235586747844991847520937 2426690060883743885640703)
                      ·
                        rfl

theorem cell23_4725962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_4725962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725962 prefixEnd_4725962 := by exact prefixLift 4725962
  have htrace : WordTrace (prefixWord ++ tailWord_4725962) baseStart_4725962 baseEnd_4725962 := by
    simpa [prefixWord, tailWord_4725962, baseEnd_4725962] using wordTrace_append hprefix tailTrace_4725962
  have hstable : (prefixWord ++ tailWord_4725962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725962).length < 2 ^ (prefixWord ++ tailWord_4725962).sum := by decide
  have hdescent : baseEnd_4725962 < baseStart_4725962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725965 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4725965 : Nat := 118140960795 + 4725965 * 2 ^ 59
def prefixEnd_4725965 : Nat := 4983230072969 + 3 ^ 40 * 4725965 * 2
def baseEnd_4725965 : Nat := 2426691601325707373903189

theorem tailTrace_4725965 : CollatzResearch.WordTrace tailWord_4725965 prefixEnd_4725965 2426691601325707373903189 := by
  unfold tailWord_4725965
  simp only [CollatzResearch.WordTrace]
  refine ⟨172370104323643410408163349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114913402882428940272108899 172370104323643410408163349)
  ·
    refine ⟨8079848640170784862882657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 172370104323643410408163349 8079848640170784862882657)
    ·
      refine ⟨6059886480128088647161993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8079848640170784862882657 6059886480128088647161993)
      ·
        refine ⟨4544914860096066485371495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6059886480128088647161993 4544914860096066485371495)
        ·
          refine ⟨6817372290144099728057243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4544914860096066485371495 6817372290144099728057243)
          ·
            refine ⟨10226058435216149592085865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6817372290144099728057243 10226058435216149592085865)
            ·
              refine ⟨7669543826412112194064399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10226058435216149592085865 7669543826412112194064399)
              ·
                refine ⟨11504315739618168291096599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7669543826412112194064399 11504315739618168291096599)
                ·
                  refine ⟨17256473609427252436644899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11504315739618168291096599 17256473609427252436644899)
                  ·
                    refine ⟨25884710414140878654967349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17256473609427252436644899 25884710414140878654967349)
                    ·
                      refine ⟨2426691601325707373903189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25884710414140878654967349 2426691601325707373903189)
                      ·
                        rfl

theorem cell23_4725965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4725965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725965 prefixEnd_4725965 := by exact prefixLift 4725965
  have htrace : WordTrace (prefixWord ++ tailWord_4725965) baseStart_4725965 baseEnd_4725965 := by
    simpa [prefixWord, tailWord_4725965, baseEnd_4725965] using wordTrace_append hprefix tailTrace_4725965
  have hstable : (prefixWord ++ tailWord_4725965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725965).length < 2 ^ (prefixWord ++ tailWord_4725965).sum := by decide
  have hdescent : baseEnd_4725965 < baseStart_4725965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725995 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 2, 1, 3]
def baseStart_4725995 : Nat := 118140960795 + 4725995 * 2 ^ 59
def prefixEnd_4725995 : Nat := 4983230072969 + 3 ^ 40 * 4725995 * 2
def baseEnd_4725995 : Nat := 2426707005745342256528051

theorem tailTrace_4725995 : CollatzResearch.WordTrace tailWord_4725995 prefixEnd_4725995 2426707005745342256528051 := by
  unfold tailWord_4725995
  simp only [CollatzResearch.WordTrace]
  refine ⟨172371198513534725531755439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114914132342356483687836959 172371198513534725531755439)
  ·
    refine ⟨258556797770302088297633159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172371198513534725531755439 258556797770302088297633159)
    ·
      refine ⟨387835196655453132446449739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258556797770302088297633159 387835196655453132446449739)
      ·
        refine ⟨581752794983179698669674609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387835196655453132446449739 581752794983179698669674609)
        ·
          refine ⟨436314596237384774002255957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581752794983179698669674609 436314596237384774002255957)
          ·
            refine ⟨5113061674656852820338937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 436314596237384774002255957 5113061674656852820338937)
            ·
              refine ⟨3834796255992639615254203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5113061674656852820338937 3834796255992639615254203)
              ·
                refine ⟨5752194383988959422881305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834796255992639615254203 5752194383988959422881305)
                ·
                  refine ⟨4314145787991719567160979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5752194383988959422881305 4314145787991719567160979)
                  ·
                    refine ⟨6471218681987579350741469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4314145787991719567160979 6471218681987579350741469)
                    ·
                      refine ⟨2426707005745342256528051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6471218681987579350741469 2426707005745342256528051)
                      ·
                        rfl

theorem cell23_4725995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 1, 3].length) (baseStart_4725995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725995 prefixEnd_4725995 := by exact prefixLift 4725995
  have htrace : WordTrace (prefixWord ++ tailWord_4725995) baseStart_4725995 baseEnd_4725995 := by
    simpa [prefixWord, tailWord_4725995, baseEnd_4725995] using wordTrace_append hprefix tailTrace_4725995
  have hstable : (prefixWord ++ tailWord_4725995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725995).length < 2 ^ (prefixWord ++ tailWord_4725995).sum := by decide
  have hdescent : baseEnd_4725995 < baseStart_4725995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726001 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 1, 4, 2]
def baseStart_4726001 : Nat := 118140960795 + 4726001 * 2 ^ 59
def prefixEnd_4726001 : Nat := 4983230072969 + 3 ^ 40 * 4726001 * 2
def baseEnd_4726001 : Nat := 2426710086629269233053023

theorem tailTrace_4726001 : CollatzResearch.WordTrace tailWord_4726001 prefixEnd_4726001 2426710086629269233053023 := by
  unfold tailWord_4726001
  simp only [CollatzResearch.WordTrace]
  refine ⟨172371417351512988556473857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114914278234341992370982571 172371417351512988556473857)
  ·
    refine ⟨129278563013634741417355393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172371417351512988556473857 129278563013634741417355393)
    ·
      refine ⟨96958922260226056063016545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129278563013634741417355393 96958922260226056063016545)
      ·
        refine ⟨72719191695169542047262409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96958922260226056063016545 72719191695169542047262409)
        ·
          refine ⟨54539393771377156535446807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72719191695169542047262409 54539393771377156535446807)
          ·
            refine ⟨81809090657065734803170211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54539393771377156535446807 81809090657065734803170211)
            ·
              refine ⟨122713635985598602204755317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81809090657065734803170211 122713635985598602204755317)
              ·
                refine ⟨11504403373649868956695811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122713635985598602204755317 11504403373649868956695811)
                ·
                  refine ⟨17256605060474803435043717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11504403373649868956695811 17256605060474803435043717)
                  ·
                    refine ⟨3235613448839025644070697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17256605060474803435043717 3235613448839025644070697)
                    ·
                      refine ⟨2426710086629269233053023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235613448839025644070697 2426710086629269233053023)
                      ·
                        rfl

theorem cell23_4726001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_4726001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726001 prefixEnd_4726001 := by exact prefixLift 4726001
  have htrace : WordTrace (prefixWord ++ tailWord_4726001) baseStart_4726001 baseEnd_4726001 := by
    simpa [prefixWord, tailWord_4726001, baseEnd_4726001] using wordTrace_append hprefix tailTrace_4726001
  have hstable : (prefixWord ++ tailWord_4726001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726001).length < 2 ^ (prefixWord ++ tailWord_4726001).sum := by decide
  have hdescent : baseEnd_4726001 < baseStart_4726001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726051 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 3]
def baseStart_4726051 : Nat := 118140960795 + 4726051 * 2 ^ 59
def prefixEnd_4726051 : Nat := 4983230072969 + 3 ^ 40 * 4726051 * 2
def baseEnd_4726051 : Nat := 2426735760661994037427793

theorem tailTrace_4726051 : CollatzResearch.WordTrace tailWord_4726051 prefixEnd_4726051 2426735760661994037427793 := by
  unfold tailWord_4726051
  simp only [CollatzResearch.WordTrace]
  refine ⟨172373241001331847095794007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114915494000887898063862671 172373241001331847095794007)
  ·
    refine ⟨258559861501997770643691011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172373241001331847095794007 258559861501997770643691011)
    ·
      refine ⟨387839792252996655965536517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258559861501997770643691011 387839792252996655965536517)
      ·
        refine ⟨72719961047436872993538097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 387839792252996655965536517 72719961047436872993538097)
        ·
          refine ⟨54539970785577654745153573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72719961047436872993538097 54539970785577654745153573)
          ·
            refine ⟨10226244522295810264716295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54539970785577654745153573 10226244522295810264716295)
            ·
              refine ⟨15339366783443715397074443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10226244522295810264716295 15339366783443715397074443)
              ·
                refine ⟨23009050175165573095611665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15339366783443715397074443 23009050175165573095611665)
                ·
                  refine ⟨17256787631374179821708749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23009050175165573095611665 17256787631374179821708749)
                  ·
                    refine ⟨6471295361765317433140781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17256787631374179821708749 6471295361765317433140781)
                    ·
                      refine ⟨2426735760661994037427793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6471295361765317433140781 2426735760661994037427793)
                      ·
                        rfl

theorem cell23_4726051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_4726051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726051 prefixEnd_4726051 := by exact prefixLift 4726051
  have htrace : WordTrace (prefixWord ++ tailWord_4726051) baseStart_4726051 baseEnd_4726051 := by
    simpa [prefixWord, tailWord_4726051, baseEnd_4726051] using wordTrace_append hprefix tailTrace_4726051
  have hstable : (prefixWord ++ tailWord_4726051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726051).length < 2 ^ (prefixWord ++ tailWord_4726051).sum := by decide
  have hdescent : baseEnd_4726051 < baseStart_4726051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726104 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_4726104 : Nat := 118140960795 + 4726104 * 2 ^ 59
def prefixEnd_4726104 : Nat := 4983230072969 + 3 ^ 40 * 4726104 * 2
def baseEnd_4726104 : Nat := 2426762975136682330065049

theorem tailTrace_4726104 : CollatzResearch.WordTrace tailWord_4726104 prefixEnd_4726104 2426762975136682330065049 := by
  unfold tailWord_4726104
  simp only [CollatzResearch.WordTrace]
  refine ⟨86187587035069918573736683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114916782713426558098315577 86187587035069918573736683)
  ·
    refine ⟨129281380552604877860605025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86187587035069918573736683 129281380552604877860605025)
    ·
      refine ⟨96961035414453658395453769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129281380552604877860605025 96961035414453658395453769)
      ·
        refine ⟨72720776560840243796590327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96961035414453658395453769 72720776560840243796590327)
        ·
          refine ⟨109081164841260365694885491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72720776560840243796590327 109081164841260365694885491)
          ·
            refine ⟨163621747261890548542328237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109081164841260365694885491 163621747261890548542328237)
            ·
              refine ⟨61358155223208955703373089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163621747261890548542328237 61358155223208955703373089)
              ·
                refine ⟨46018616417406716777529817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61358155223208955703373089 46018616417406716777529817)
                ·
                  refine ⟨34513962313055037583147363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46018616417406716777529817 34513962313055037583147363)
                  ·
                    refine ⟨51770943469582556374721045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34513962313055037583147363 51770943469582556374721045)
                    ·
                      refine ⟨2426762975136682330065049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51770943469582556374721045 2426762975136682330065049)
                      ·
                        rfl

theorem cell23_4726104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_4726104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726104 prefixEnd_4726104 := by exact prefixLift 4726104
  have htrace : WordTrace (prefixWord ++ tailWord_4726104) baseStart_4726104 baseEnd_4726104 := by
    simpa [prefixWord, tailWord_4726104, baseEnd_4726104] using wordTrace_append hprefix tailTrace_4726104
  have hstable : (prefixWord ++ tailWord_4726104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726104).length < 2 ^ (prefixWord ++ tailWord_4726104).sum := by decide
  have hdescent : baseEnd_4726104 < baseStart_4726104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726142 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4726142 : Nat := 118140960795 + 4726142 * 2 ^ 59
def prefixEnd_4726142 : Nat := 4983230072969 + 3 ^ 40 * 4726142 * 2
def baseEnd_4726142 : Nat := 2426782487401553181389875

theorem tailTrace_4726142 : CollatzResearch.WordTrace tailWord_4726142 prefixEnd_4726142 2426782487401553181389875 := by
  unfold tailWord_4726142
  simp only [CollatzResearch.WordTrace]
  refine ⟨21547070005500271204669585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114917706696001446424904453 21547070005500271204669585)
  ·
    refine ⟨16160302504125203403502189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21547070005500271204669585 16160302504125203403502189)
    ·
      refine ⟨6060113439046951276313321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16160302504125203403502189 6060113439046951276313321)
      ·
        refine ⟨4545085079285213457234991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6060113439046951276313321 4545085079285213457234991)
        ·
          refine ⟨6817627618927820185852487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4545085079285213457234991 6817627618927820185852487)
          ·
            refine ⟨10226441428391730278778731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6817627618927820185852487 10226441428391730278778731)
            ·
              refine ⟨15339662142587595418168097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10226441428391730278778731 15339662142587595418168097)
              ·
                refine ⟨11504746606940696563626073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15339662142587595418168097 11504746606940696563626073)
                ·
                  refine ⟨8628559955205522422719555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11504746606940696563626073 8628559955205522422719555)
                  ·
                    refine ⟨12942839932808283634079333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8628559955205522422719555 12942839932808283634079333)
                    ·
                      refine ⟨2426782487401553181389875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12942839932808283634079333 2426782487401553181389875)
                      ·
                        rfl

theorem cell23_4726142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4726142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726142 prefixEnd_4726142 := by exact prefixLift 4726142
  have htrace : WordTrace (prefixWord ++ tailWord_4726142) baseStart_4726142 baseEnd_4726142 := by
    simpa [prefixWord, tailWord_4726142, baseEnd_4726142] using wordTrace_append hprefix tailTrace_4726142
  have hstable : (prefixWord ++ tailWord_4726142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726142).length < 2 ^ (prefixWord ++ tailWord_4726142).sum := by decide
  have hdescent : baseEnd_4726142 < baseStart_4726142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726145 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_4726145 : Nat := 118140960795 + 4726145 * 2 ^ 59
def prefixEnd_4726145 : Nat := 4983230072969 + 3 ^ 40 * 4726145 * 2
def baseEnd_4726145 : Nat := 2426784027843516669652361

theorem tailTrace_4726145 : CollatzResearch.WordTrace tailWord_4726145 prefixEnd_4726145 2426784027843516669652361 := by
  unfold tailWord_4726145
  simp only [CollatzResearch.WordTrace]
  refine ⟨172376669462991301149715889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114917779641994200766477259 172376669462991301149715889)
  ·
    refine ⟨129282502097243475862286917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172376669462991301149715889 129282502097243475862286917)
    ·
      refine ⟨24240469143233151724178797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129282502097243475862286917 24240469143233151724178797)
      ·
        refine ⟨9090175928712431896567049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24240469143233151724178797 9090175928712431896567049)
        ·
          refine ⟨6817631946534323922425287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9090175928712431896567049 6817631946534323922425287)
          ·
            refine ⟨10226447919801485883637931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6817631946534323922425287 10226447919801485883637931)
            ·
              refine ⟨15339671879702228825456897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10226447919801485883637931 15339671879702228825456897)
              ·
                refine ⟨11504753909776671619092673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15339671879702228825456897 11504753909776671619092673)
                ·
                  refine ⟨8628565432332503714319505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11504753909776671619092673 8628565432332503714319505)
                  ·
                    refine ⟨6471424074249377785739629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8628565432332503714319505 6471424074249377785739629)
                    ·
                      refine ⟨2426784027843516669652361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6471424074249377785739629 2426784027843516669652361)
                      ·
                        rfl

theorem cell23_4726145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_4726145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726145 prefixEnd_4726145 := by exact prefixLift 4726145
  have htrace : WordTrace (prefixWord ++ tailWord_4726145) baseStart_4726145 baseEnd_4726145 := by
    simpa [prefixWord, tailWord_4726145, baseEnd_4726145] using wordTrace_append hprefix tailTrace_4726145
  have hstable : (prefixWord ++ tailWord_4726145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726145).length < 2 ^ (prefixWord ++ tailWord_4726145).sum := by decide
  have hdescent : baseEnd_4726145 < baseStart_4726145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726152 : List Nat := [2, 1, 3, 3, 1, 3, 3, 2, 1, 4]
def baseStart_4726152 : Nat := 118140960795 + 4726152 * 2 ^ 59
def prefixEnd_4726152 : Nat := 4983230072969 + 3 ^ 40 * 4726152 * 2
def baseEnd_4726152 : Nat := 808929207402699380754943

theorem tailTrace_4726152 : CollatzResearch.WordTrace tailWord_4726152 prefixEnd_4726152 808929207402699380754943 := by
  unfold tailWord_4726152
  simp only [CollatzResearch.WordTrace]
  refine ⟨86188462386982970672610355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114917949849310627563480473 86188462386982970672610355)
  ·
    refine ⟨129282693580474456008915533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86188462386982970672610355 129282693580474456008915533)
    ·
      refine ⟨48481010092677921003343325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129282693580474456008915533 48481010092677921003343325)
      ·
        refine ⟨18180378784754220376253747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48481010092677921003343325 18180378784754220376253747)
        ·
          refine ⟨27270568177131330564380621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18180378784754220376253747 27270568177131330564380621)
          ·
            refine ⟨10226463066424248961642733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27270568177131330564380621 10226463066424248961642733)
            ·
              refine ⟨3834923649909093360616025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10226463066424248961642733 3834923649909093360616025)
              ·
                refine ⟨2876192737431820020462019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834923649909093360616025 2876192737431820020462019)
                ·
                  refine ⟨4314289106147730030693029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876192737431820020462019 4314289106147730030693029)
                  ·
                    refine ⟨808929207402699380754943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4314289106147730030693029 808929207402699380754943)
                    ·
                      rfl

theorem cell23_4726152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_4726152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726152 prefixEnd_4726152 := by exact prefixLift 4726152
  have htrace : WordTrace (prefixWord ++ tailWord_4726152) baseStart_4726152 baseEnd_4726152 := by
    simpa [prefixWord, tailWord_4726152, baseEnd_4726152] using wordTrace_append hprefix tailTrace_4726152
  have hstable : (prefixWord ++ tailWord_4726152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726152).length < 2 ^ (prefixWord ++ tailWord_4726152).sum := by decide
  have hdescent : baseEnd_4726152 < baseStart_4726152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726178 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_4726178 : Nat := 118140960795 + 4726178 * 2 ^ 59
def prefixEnd_4726178 : Nat := 4983230072969 + 3 ^ 40 * 4726178 * 2
def baseEnd_4726178 : Nat := 808933657568371680179903

theorem tailTrace_4726178 : CollatzResearch.WordTrace tailWord_4726178 prefixEnd_4726178 808933657568371680179903 := by
  unfold tailWord_4726178
  simp only [CollatzResearch.WordTrace]
  refine ⟨43094468267967936946416797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114918582047914498523778125 43094468267967936946416797)
  ·
    refine ⟨16160425600487976354906299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43094468267967936946416797 16160425600487976354906299)
    ·
      refine ⟨24240638400731964532359449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16160425600487976354906299 24240638400731964532359449)
      ·
        refine ⟨18180478800548973399269587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24240638400731964532359449 18180478800548973399269587)
        ·
          refine ⟨27270718200823460098904381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18180478800548973399269587 27270718200823460098904381)
          ·
            refine ⟨10226519325308797537089143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27270718200823460098904381 10226519325308797537089143)
            ·
              refine ⟨15339778987963196305633715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10226519325308797537089143 15339778987963196305633715)
              ·
                refine ⟨23009668481944794458450573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15339778987963196305633715 23009668481944794458450573)
                ·
                  refine ⟨8628625680729297921918965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23009668481944794458450573 8628625680729297921918965)
                  ·
                    refine ⟨808933657568371680179903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8628625680729297921918965 808933657568371680179903)
                    ·
                      rfl

theorem cell23_4726178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_4726178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726178 prefixEnd_4726178 := by exact prefixLift 4726178
  have htrace : WordTrace (prefixWord ++ tailWord_4726178) baseStart_4726178 baseEnd_4726178 := by
    simpa [prefixWord, tailWord_4726178, baseEnd_4726178] using wordTrace_append hprefix tailTrace_4726178
  have hstable : (prefixWord ++ tailWord_4726178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726178).length < 2 ^ (prefixWord ++ tailWord_4726178).sum := by decide
  have hdescent : baseEnd_4726178 < baseStart_4726178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726191 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 6, 4]
def baseStart_4726191 : Nat := 118140960795 + 4726191 * 2 ^ 59
def prefixEnd_4726191 : Nat := 4983230072969 + 3 ^ 40 * 4726191 * 2
def baseEnd_4726191 : Nat := 808935882651207829892383

theorem tailTrace_4726191 : CollatzResearch.WordTrace tailWord_4726191 prefixEnd_4726191 808935882651207829892383 := by
  unfold tailWord_4726191
  simp only [CollatzResearch.WordTrace]
  refine ⟨172378347220824651005890427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114918898147216434003926951 172378347220824651005890427)
  ·
    refine ⟨258567520831236976508835641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172378347220824651005890427 258567520831236976508835641)
    ·
      refine ⟨193925640623427732381626731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258567520831236976508835641 193925640623427732381626731)
      ·
        refine ⟨290888460935141598572440097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193925640623427732381626731 290888460935141598572440097)
        ·
          refine ⟨218166345701356198929330073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290888460935141598572440097 218166345701356198929330073)
          ·
            refine ⟨163624759276017149196997555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218166345701356198929330073 163624759276017149196997555)
            ·
              refine ⟨245437138914025723795496333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163624759276017149196997555 245437138914025723795496333)
              ·
                refine ⟨92038927092759646423311125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245437138914025723795496333 92038927092759646423311125)
                ·
                  refine ⟨4314324707473108426092709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92038927092759646423311125 4314324707473108426092709)
                  ·
                    refine ⟨808935882651207829892383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4314324707473108426092709 808935882651207829892383)
                    ·
                      rfl

theorem cell23_4726191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 4].length) (baseStart_4726191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726191 prefixEnd_4726191 := by exact prefixLift 4726191
  have htrace : WordTrace (prefixWord ++ tailWord_4726191) baseStart_4726191 baseEnd_4726191 := by
    simpa [prefixWord, tailWord_4726191, baseEnd_4726191] using wordTrace_append hprefix tailTrace_4726191
  have hstable : (prefixWord ++ tailWord_4726191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726191).length < 2 ^ (prefixWord ++ tailWord_4726191).sum := by decide
  have hdescent : baseEnd_4726191 < baseStart_4726191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726208 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 2, 4]
def baseStart_4726208 : Nat := 118140960795 + 4726208 * 2 ^ 59
def prefixEnd_4726208 : Nat := 4983230072969 + 3 ^ 40 * 4726208 * 2
def baseEnd_4726208 : Nat := 808938792374916641054857

theorem tailTrace_4726208 : CollatzResearch.WordTrace tailWord_4726208 prefixEnd_4726208 808938792374916641054857 := by
  unfold tailWord_4726208
  simp only [CollatzResearch.WordTrace]
  refine ⟨86189483630881531454629639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114919311507842041939506185 86189483630881531454629639)
  ·
    refine ⟨129284225446322297181944459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86189483630881531454629639 129284225446322297181944459)
    ·
      refine ⟨193926338169483445772916689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129284225446322297181944459 193926338169483445772916689)
      ·
        refine ⟨145444753627112584329687517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193926338169483445772916689 145444753627112584329687517)
        ·
          refine ⟨54541782610167219123632819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145444753627112584329687517 54541782610167219123632819)
          ·
            refine ⟨81812673915250828685449229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54541782610167219123632819 81812673915250828685449229)
            ·
              refine ⟨30679752718219060757043461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81812673915250828685449229 30679752718219060757043461)
              ·
                refine ⟨5752453634666073891945649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30679752718219060757043461 5752453634666073891945649)
                ·
                  refine ⟨4314340225999555418959237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5752453634666073891945649 4314340225999555418959237)
                  ·
                    refine ⟨808938792374916641054857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4314340225999555418959237 808938792374916641054857)
                    ·
                      rfl

theorem cell23_4726208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2, 4].length) (baseStart_4726208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726208 prefixEnd_4726208 := by exact prefixLift 4726208
  have htrace : WordTrace (prefixWord ++ tailWord_4726208) baseStart_4726208 baseEnd_4726208 := by
    simpa [prefixWord, tailWord_4726208, baseEnd_4726208] using wordTrace_append hprefix tailTrace_4726208
  have hstable : (prefixWord ++ tailWord_4726208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726208).length < 2 ^ (prefixWord ++ tailWord_4726208).sum := by decide
  have hdescent : baseEnd_4726208 < baseStart_4726208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726215 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_4726215 : Nat := 118140960795 + 4726215 * 2 ^ 59
def prefixEnd_4726215 : Nat := 4983230072969 + 3 ^ 40 * 4726215 * 2
def baseEnd_4726215 : Nat := 2426819971489331395777039

theorem tailTrace_4726215 : CollatzResearch.WordTrace tailWord_4726215 prefixEnd_4726215 2426819971489331395777039 := by
  unfold tailWord_4726215
  simp only [CollatzResearch.WordTrace]
  refine ⟨172379222572737703104764099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114919481715158468736509399 172379222572737703104764099)
  ·
    refine ⟨258568833859106554657146149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172379222572737703104764099 258568833859106554657146149)
    ·
      refine ⟨48481656348582478998214903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258568833859106554657146149 48481656348582478998214903)
      ·
        refine ⟨72722484522873718497322355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48481656348582478998214903 72722484522873718497322355)
        ·
          refine ⟨109083726784310577745983533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72722484522873718497322355 109083726784310577745983533)
          ·
            refine ⟨40906397544116466654743825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109083726784310577745983533 40906397544116466654743825)
            ·
              refine ⟨30679798158087349991057869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40906397544116466654743825 30679798158087349991057869)
              ·
                refine ⟨11504924309282756246646701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30679798158087349991057869 11504924309282756246646701)
                ·
                  refine ⟨4314346615981033592492513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11504924309282756246646701 4314346615981033592492513)
                  ·
                    refine ⟨3235759961985775194369385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4314346615981033592492513 3235759961985775194369385)
                    ·
                      refine ⟨2426819971489331395777039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235759961985775194369385 2426819971489331395777039)
                      ·
                        rfl

theorem cell23_4726215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_4726215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726215 prefixEnd_4726215 := by exact prefixLift 4726215
  have htrace : WordTrace (prefixWord ++ tailWord_4726215) baseStart_4726215 baseEnd_4726215 := by
    simpa [prefixWord, tailWord_4726215, baseEnd_4726215] using wordTrace_append hprefix tailTrace_4726215
  have hstable : (prefixWord ++ tailWord_4726215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726215).length < 2 ^ (prefixWord ++ tailWord_4726215).sum := by decide
  have hdescent : baseEnd_4726215 < baseStart_4726215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726218 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_4726218 : Nat := 118140960795 + 4726218 * 2 ^ 59
def prefixEnd_4726218 : Nat := 4983230072969 + 3 ^ 40 * 4726218 * 2
def baseEnd_4726218 : Nat := 2426821511931294884039525

theorem tailTrace_4726218 : CollatzResearch.WordTrace tailWord_4726218 prefixEnd_4726218 2426821511931294884039525 := by
  unfold tailWord_4726218
  simp only [CollatzResearch.WordTrace]
  refine ⟨43094832997931708654280827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114919554661151223078082205 43094832997931708654280827)
  ·
    refine ⟨64642249496897562981421241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43094832997931708654280827 64642249496897562981421241)
    ·
      refine ⟨48481687122673172236065931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64642249496897562981421241 48481687122673172236065931)
      ·
        refine ⟨72722530684009758354098897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48481687122673172236065931 72722530684009758354098897)
        ·
          refine ⟨54541898013007318765574173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72722530684009758354098897 54541898013007318765574173)
          ·
            refine ⟨20453211754877744537090315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54541898013007318765574173 20453211754877744537090315)
            ·
              refine ⟨30679817632316616805635473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20453211754877744537090315 30679817632316616805635473)
              ·
                refine ⟨23009863224237462604226605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30679817632316616805635473 23009863224237462604226605)
                ·
                  refine ⟨8628698709089048476584977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23009863224237462604226605 8628698709089048476584977)
                  ·
                    refine ⟨6471524031816786357438733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8628698709089048476584977 6471524031816786357438733)
                    ·
                      refine ⟨2426821511931294884039525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6471524031816786357438733 2426821511931294884039525)
                      ·
                        rfl

theorem cell23_4726218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_4726218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726218 prefixEnd_4726218 := by exact prefixLift 4726218
  have htrace : WordTrace (prefixWord ++ tailWord_4726218) baseStart_4726218 baseEnd_4726218 := by
    simpa [prefixWord, tailWord_4726218, baseEnd_4726218] using wordTrace_append hprefix tailTrace_4726218
  have hstable : (prefixWord ++ tailWord_4726218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726218).length < 2 ^ (prefixWord ++ tailWord_4726218).sum := by decide
  have hdescent : baseEnd_4726218 < baseStart_4726218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726248 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_4726248 : Nat := 118140960795 + 4726248 * 2 ^ 59
def prefixEnd_4726248 : Nat := 4983230072969 + 3 ^ 40 * 4726248 * 2
def baseEnd_4726248 : Nat := 2426836916350929766664387

theorem tailTrace_4726248 : CollatzResearch.WordTrace tailWord_4726248 prefixEnd_4726248 2426836916350929766664387 := by
  unfold tailWord_4726248
  simp only [CollatzResearch.WordTrace]
  refine ⟨86190213090809074870357699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114920284121078766493810265 86190213090809074870357699)
  ·
    refine ⟨129285319636213612305536549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86190213090809074870357699 129285319636213612305536549)
    ·
      refine ⟨24240997431790052307288103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129285319636213612305536549 24240997431790052307288103)
      ·
        refine ⟨36361496147685078460932155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24240997431790052307288103 36361496147685078460932155)
        ·
          refine ⟨54542244221527617691398233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36361496147685078460932155 54542244221527617691398233)
          ·
            refine ⟨40906683166145713268548675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54542244221527617691398233 40906683166145713268548675)
            ·
              refine ⟨61360024749218569902823013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40906683166145713268548675 61360024749218569902823013)
              ·
                refine ⟨11505004640478481856779315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61360024749218569902823013 11505004640478481856779315)
                ·
                  refine ⟨17257506960717722785168973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11505004640478481856779315 17257506960717722785168973)
                  ·
                    refine ⟨6471565110269146044438365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17257506960717722785168973 6471565110269146044438365)
                    ·
                      refine ⟨2426836916350929766664387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6471565110269146044438365 2426836916350929766664387)
                      ·
                        rfl

theorem cell23_4726248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_4726248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726248 prefixEnd_4726248 := by exact prefixLift 4726248
  have htrace : WordTrace (prefixWord ++ tailWord_4726248) baseStart_4726248 baseEnd_4726248 := by
    simpa [prefixWord, tailWord_4726248, baseEnd_4726248] using wordTrace_append hprefix tailTrace_4726248
  have hstable : (prefixWord ++ tailWord_4726248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726248).length < 2 ^ (prefixWord ++ tailWord_4726248).sum := by decide
  have hdescent : baseEnd_4726248 < baseStart_4726248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726271 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_4726271 : Nat := 118140960795 + 4726271 * 2 ^ 59
def prefixEnd_4726271 : Nat := 4983230072969 + 3 ^ 40 * 4726271 * 2
def baseEnd_4726271 : Nat := 2426848726405983176676781

theorem tailTrace_4726271 : CollatzResearch.WordTrace tailWord_4726271 prefixEnd_4726271 2426848726405983176676781 := by
  unfold tailWord_4726271
  simp only [CollatzResearch.WordTrace]
  refine ⟨172381265060534824668802667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114920843373689883112535111 172381265060534824668802667)
  ·
    refine ⟨258571897590802237003204001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172381265060534824668802667 258571897590802237003204001)
    ·
      refine ⟨193928923193101677752403001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258571897590802237003204001 193928923193101677752403001)
      ·
        refine ⟨145446692394826258314302251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193928923193101677752403001 145446692394826258314302251)
        ·
          refine ⟨218170038592239387471453377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145446692394826258314302251 218170038592239387471453377)
          ·
            refine ⟨163627528944179540603590033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218170038592239387471453377 163627528944179540603590033)
            ·
              refine ⟨122720646708134655452692525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163627528944179540603590033 122720646708134655452692525)
              ·
                refine ⟨46020242515550495794759697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122720646708134655452692525 46020242515550495794759697)
                ·
                  refine ⟨34515181886662871846069773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46020242515550495794759697 34515181886662871846069773)
                  ·
                    refine ⟨12943193207498576942276165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34515181886662871846069773 12943193207498576942276165)
                    ·
                      refine ⟨2426848726405983176676781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12943193207498576942276165 2426848726405983176676781)
                      ·
                        rfl

theorem cell23_4726271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_4726271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726271 prefixEnd_4726271 := by exact prefixLift 4726271
  have htrace : WordTrace (prefixWord ++ tailWord_4726271) baseStart_4726271 baseEnd_4726271 := by
    simpa [prefixWord, tailWord_4726271, baseEnd_4726271] using wordTrace_append hprefix tailTrace_4726271
  have hstable : (prefixWord ++ tailWord_4726271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726271).length < 2 ^ (prefixWord ++ tailWord_4726271).sum := by decide
  have hdescent : baseEnd_4726271 < baseStart_4726271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726281 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 2, 6]
def baseStart_4726281 : Nat := 118140960795 + 4726281 * 2 ^ 59
def prefixEnd_4726281 : Nat := 4983230072969 + 3 ^ 40 * 4726281 * 2
def baseEnd_4726281 : Nat := 808951287070842712517245

theorem tailTrace_4726281 : CollatzResearch.WordTrace tailWord_4726281 prefixEnd_4726281 808951287070842712517245 := by
  unfold tailWord_4726281
  simp only [CollatzResearch.WordTrace]
  refine ⟨172381629790498596376666697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114921086526999064251111131 172381629790498596376666697)
  ·
    refine ⟨129286222342873947282500023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172381629790498596376666697 129286222342873947282500023)
    ·
      refine ⟨193929333514310920923750035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129286222342873947282500023 193929333514310920923750035)
      ·
        refine ⟨290894000271466381385625053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193929333514310920923750035 290894000271466381385625053)
        ·
          refine ⟨109085250101799893019609395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290894000271466381385625053 109085250101799893019609395)
          ·
            refine ⟨163627875152699839529414093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109085250101799893019609395 163627875152699839529414093)
            ·
              refine ⟨61360453182262439823530285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163627875152699839529414093 61360453182262439823530285)
              ·
                refine ⟨23010169943348414933823857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61360453182262439823530285 23010169943348414933823857)
                ·
                  refine ⟨17257627457511311200367893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23010169943348414933823857 17257627457511311200367893)
                  ·
                    refine ⟨808951287070842712517245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17257627457511311200367893 808951287070842712517245)
                    ·
                      rfl

theorem cell23_4726281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_4726281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726281 prefixEnd_4726281 := by exact prefixLift 4726281
  have htrace : WordTrace (prefixWord ++ tailWord_4726281) baseStart_4726281 baseEnd_4726281 := by
    simpa [prefixWord, tailWord_4726281, baseEnd_4726281] using wordTrace_append hprefix tailTrace_4726281
  have hstable : (prefixWord ++ tailWord_4726281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726281).length < 2 ^ (prefixWord ++ tailWord_4726281).sum := by decide
  have hdescent : baseEnd_4726281 < baseStart_4726281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726321 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_4726321 : Nat := 118140960795 + 4726321 * 2 ^ 59
def prefixEnd_4726321 : Nat := 4983230072969 + 3 ^ 40 * 4726321 * 2
def baseEnd_4726321 : Nat := 2426874400438707981051551

theorem tailTrace_4726321 : CollatzResearch.WordTrace tailWord_4726321 prefixEnd_4726321 2426874400438707981051551 := by
  unfold tailWord_4726321
  simp only [CollatzResearch.WordTrace]
  refine ⟨172383088710353683208122817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114922059140235788805415211 172383088710353683208122817)
  ·
    refine ⟨129287316532765262406092113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172383088710353683208122817 129287316532765262406092113)
    ·
      refine ⟨96965487399573946804569085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129287316532765262406092113 96965487399573946804569085)
      ·
        refine ⟨36362057774840230051713407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96965487399573946804569085 36362057774840230051713407)
        ·
          refine ⟨54543086662260345077570111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36362057774840230051713407 54543086662260345077570111)
          ·
            refine ⟨81814629993390517616355167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54543086662260345077570111 81814629993390517616355167)
            ·
              refine ⟨122721944990085776424532751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81814629993390517616355167 122721944990085776424532751)
              ·
                refine ⟨184082917485128664636799127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122721944990085776424532751 184082917485128664636799127)
                ·
                  refine ⟨276124376227692996955198691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184082917485128664636799127 276124376227692996955198691)
                  ·
                    refine ⟨414186564341539495432798037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 276124376227692996955198691 414186564341539495432798037)
                    ·
                      refine ⟨2426874400438707981051551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 414186564341539495432798037 2426874400438707981051551)
                      ·
                        rfl

theorem cell23_4726321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_4726321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726321 prefixEnd_4726321 := by exact prefixLift 4726321
  have htrace : WordTrace (prefixWord ++ tailWord_4726321) baseStart_4726321 baseEnd_4726321 := by
    simpa [prefixWord, tailWord_4726321, baseEnd_4726321] using wordTrace_append hprefix tailTrace_4726321
  have hstable : (prefixWord ++ tailWord_4726321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726321).length < 2 ^ (prefixWord ++ tailWord_4726321).sum := by decide
  have hdescent : baseEnd_4726321 < baseStart_4726321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726322 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_4726322 : Nat := 118140960795 + 4726322 * 2 ^ 59
def prefixEnd_4726322 : Nat := 4983230072969 + 3 ^ 40 * 4726322 * 2
def baseEnd_4726322 : Nat := 2426874913919362477139047

theorem tailTrace_4726322 : CollatzResearch.WordTrace tailWord_4726322 prefixEnd_4726322 2426874913919362477139047 := by
  unfold tailWord_4726322
  simp only [CollatzResearch.WordTrace]
  refine ⟨43095781295837515094727305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114922083455566706919272813 43095781295837515094727305)
  ·
    refine ⟨32321835971878136321045479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43095781295837515094727305 32321835971878136321045479)
    ·
      refine ⟨48482753957817204481568219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32321835971878136321045479 48482753957817204481568219)
      ·
        refine ⟨72724130936725806722352329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48482753957817204481568219 72724130936725806722352329)
        ·
          refine ⟨54543098202544355041764247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72724130936725806722352329 54543098202544355041764247)
          ·
            refine ⟨81814647303816532562646371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54543098202544355041764247 81814647303816532562646371)
            ·
              refine ⟨122721970955724798843969557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81814647303816532562646371 122721970955724798843969557)
              ·
                refine ⟨5752592388549599945811073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122721970955724798843969557 5752592388549599945811073)
                ·
                  refine ⟨4314444291412199959358305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5752592388549599945811073 4314444291412199959358305)
                  ·
                    refine ⟨3235833218559149969518729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4314444291412199959358305 3235833218559149969518729)
                    ·
                      refine ⟨2426874913919362477139047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235833218559149969518729 2426874913919362477139047)
                      ·
                        rfl

theorem cell23_4726322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_4726322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726322 prefixEnd_4726322 := by exact prefixLift 4726322
  have htrace : WordTrace (prefixWord ++ tailWord_4726322) baseStart_4726322 baseEnd_4726322 := by
    simpa [prefixWord, tailWord_4726322, baseEnd_4726322] using wordTrace_append hprefix tailTrace_4726322
  have hstable : (prefixWord ++ tailWord_4726322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726322).length < 2 ^ (prefixWord ++ tailWord_4726322).sum := by decide
  have hdescent : baseEnd_4726322 < baseStart_4726322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726328 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 7]
def baseStart_4726328 : Nat := 118140960795 + 4726328 * 2 ^ 59
def prefixEnd_4726328 : Nat := 4983230072969 + 3 ^ 40 * 4726328 * 2
def baseEnd_4726328 : Nat := 269653110533698828184891

theorem tailTrace_4726328 : CollatzResearch.WordTrace tailWord_4726328 prefixEnd_4726328 269653110533698828184891 := by
  unfold tailWord_4726328
  simp only [CollatzResearch.WordTrace]
  refine ⟨86191672010664161701813819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114922229347552215602418425 86191672010664161701813819)
  ·
    refine ⟨129287508015996242552720729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86191672010664161701813819 129287508015996242552720729)
    ·
      refine ⟨96965631011997181914540547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129287508015996242552720729 96965631011997181914540547)
      ·
        refine ⟨145448446517995772871810821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96965631011997181914540547 145448446517995772871810821)
        ·
          refine ⟨27271583722124207413464529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145448446517995772871810821 27271583722124207413464529)
          ·
            refine ⟨20453687791593155560098397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27271583722124207413464529 20453687791593155560098397)
            ·
              refine ⟨7670132921847433335036899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20453687791593155560098397 7670132921847433335036899)
              ·
                refine ⟨11505199382771150002555349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7670132921847433335036899 11505199382771150002555349)
                ·
                  refine ⟨269653110533698828184891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11505199382771150002555349 269653110533698828184891)
                  ·
                    rfl

theorem cell23_4726328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 7].length) (baseStart_4726328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726328 prefixEnd_4726328 := by exact prefixLift 4726328
  have htrace : WordTrace (prefixWord ++ tailWord_4726328) baseStart_4726328 baseEnd_4726328 := by
    simpa [prefixWord, tailWord_4726328, baseEnd_4726328] using wordTrace_append hprefix tailTrace_4726328
  have hstable : (prefixWord ++ tailWord_4726328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726328).length < 2 ^ (prefixWord ++ tailWord_4726328).sum := by decide
  have hdescent : baseEnd_4726328 < baseStart_4726328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726351 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_4726351 : Nat := 118140960795 + 4726351 * 2 ^ 59
def prefixEnd_4726351 : Nat := 4983230072969 + 3 ^ 40 * 4726351 * 2
def baseEnd_4726351 : Nat := 2426889804858342863676413

theorem tailTrace_4726351 : CollatzResearch.WordTrace tailWord_4726351 prefixEnd_4726351 2426889804858342863676413 := by
  unfold tailWord_4726351
  simp only [CollatzResearch.WordTrace]
  refine ⟨172384182900244998331714907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114922788600163332221143271 172384182900244998331714907)
  ·
    refine ⟨258576274350367497497572361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172384182900244998331714907 258576274350367497497572361)
    ·
      refine ⟨193932205762775623123179271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258576274350367497497572361 193932205762775623123179271)
      ·
        refine ⟨290898308644163434684768907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193932205762775623123179271 290898308644163434684768907)
        ·
          refine ⟨436347462966245152027153361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290898308644163434684768907 436347462966245152027153361)
          ·
            refine ⟨327260597224683864020365021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436347462966245152027153361 327260597224683864020365021)
            ·
              refine ⟨122722723959256449007636883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327260597224683864020365021 122722723959256449007636883)
              ·
                refine ⟨184084085938884673511455325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122722723959256449007636883 184084085938884673511455325)
                ·
                  refine ⟨69031532227081752566795747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184084085938884673511455325 69031532227081752566795747)
                  ·
                    refine ⟨103547298340622628850193621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69031532227081752566795747 103547298340622628850193621)
                    ·
                      refine ⟨2426889804858342863676413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103547298340622628850193621 2426889804858342863676413)
                      ·
                        rfl

theorem cell23_4726351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_4726351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726351 prefixEnd_4726351 := by exact prefixLift 4726351
  have htrace : WordTrace (prefixWord ++ tailWord_4726351) baseStart_4726351 baseEnd_4726351 := by
    simpa [prefixWord, tailWord_4726351, baseEnd_4726351] using wordTrace_append hprefix tailTrace_4726351
  have hstable : (prefixWord ++ tailWord_4726351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726351).length < 2 ^ (prefixWord ++ tailWord_4726351).sum := by decide
  have hdescent : baseEnd_4726351 < baseStart_4726351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726395 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 2, 4, 2]
def baseStart_4726395 : Nat := 118140960795 + 4726395 * 2 ^ 59
def prefixEnd_4726395 : Nat := 4983230072969 + 3 ^ 40 * 4726395 * 2
def baseEnd_4726395 : Nat := 2426912398007140691526211

theorem tailTrace_4726395 : CollatzResearch.WordTrace tailWord_4726395 prefixEnd_4726395 2426912398007140691526211 := by
  unfold tailWord_4726395
  simp only [CollatzResearch.WordTrace]
  refine ⟨172385787712085593846316639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114923858474723729230877759 172385787712085593846316639)
  ·
    refine ⟨258578681568128390769474959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172385787712085593846316639 258578681568128390769474959)
    ·
      refine ⟨387868022352192586154212439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258578681568128390769474959 387868022352192586154212439)
      ·
        refine ⟨581802033528288879231318659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387868022352192586154212439 581802033528288879231318659)
        ·
          refine ⟨872703050292433318846977989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581802033528288879231318659 872703050292433318846977989)
          ·
            refine ⟨163631821929831247283808373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 872703050292433318846977989 163631821929831247283808373)
            ·
              refine ⟨15340483305921679432857035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163631821929831247283808373 15340483305921679432857035)
              ·
                refine ⟨23010724958882519149285553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15340483305921679432857035 23010724958882519149285553)
                ·
                  refine ⟨17258043719161889361964165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23010724958882519149285553 17258043719161889361964165)
                  ·
                    refine ⟨3235883197342854255368281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17258043719161889361964165 3235883197342854255368281)
                    ·
                      refine ⟨2426912398007140691526211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235883197342854255368281 2426912398007140691526211)
                      ·
                        rfl

theorem cell23_4726395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 4, 2].length) (baseStart_4726395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726395 prefixEnd_4726395 := by exact prefixLift 4726395
  have htrace : WordTrace (prefixWord ++ tailWord_4726395) baseStart_4726395 baseEnd_4726395 := by
    simpa [prefixWord, tailWord_4726395, baseEnd_4726395] using wordTrace_append hprefix tailTrace_4726395
  have hstable : (prefixWord ++ tailWord_4726395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726395).length < 2 ^ (prefixWord ++ tailWord_4726395).sum := by decide
  have hdescent : baseEnd_4726395 < baseStart_4726395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726405 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_4726405 : Nat := 118140960795 + 4726405 * 2 ^ 59
def prefixEnd_4726405 : Nat := 4983230072969 + 3 ^ 40 * 4726405 * 2
def baseEnd_4726405 : Nat := 808972510937895217467055

theorem tailTrace_4726405 : CollatzResearch.WordTrace tailWord_4726405 prefixEnd_4726405 808972510937895217467055 := by
  unfold tailWord_4726405
  simp only [CollatzResearch.WordTrace]
  refine ⟨172386152442049365554180669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114924101628032910369453779 172386152442049365554180669)
  ·
    refine ⟨64644807165768512082817751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172386152442049365554180669 64644807165768512082817751)
    ·
      refine ⟨96967210748652768124226627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64644807165768512082817751 96967210748652768124226627)
      ·
        refine ⟨145450816122979152186339941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96967210748652768124226627 145450816122979152186339941)
        ·
          refine ⟨27272028023058591034938739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145450816122979152186339941 27272028023058591034938739)
          ·
            refine ⟨40908042034587886552408109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27272028023058591034938739 40908042034587886552408109)
            ·
              refine ⟨15340515762970457457153041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40908042034587886552408109 15340515762970457457153041)
              ·
                refine ⟨11505386822227843092864781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15340515762970457457153041 11505386822227843092864781)
                ·
                  refine ⟨4314520058335441159824293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11505386822227843092864781 4314520058335441159824293)
                  ·
                    refine ⟨808972510937895217467055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4314520058335441159824293 808972510937895217467055)
                    ·
                      rfl

theorem cell23_4726405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_4726405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726405 prefixEnd_4726405 := by exact prefixLift 4726405
  have htrace : WordTrace (prefixWord ++ tailWord_4726405) baseStart_4726405 baseEnd_4726405 := by
    simpa [prefixWord, tailWord_4726405, baseEnd_4726405] using wordTrace_append hprefix tailTrace_4726405
  have hstable : (prefixWord ++ tailWord_4726405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726405).length < 2 ^ (prefixWord ++ tailWord_4726405).sum := by decide
  have hdescent : baseEnd_4726405 < baseStart_4726405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726448 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 5, 5]
def baseStart_4726448 : Nat := 118140960795 + 4726448 * 2 ^ 59
def prefixEnd_4726448 : Nat := 4983230072969 + 3 ^ 40 * 4726448 * 2
def baseEnd_4726448 : Nat := 808979870827276328054489

theorem tailTrace_4726448 : CollatzResearch.WordTrace tailWord_4726448 prefixEnd_4726448 808979870827276328054489 := by
  unfold tailWord_4726448
  simp only [CollatzResearch.WordTrace]
  refine ⟨86193860390446791948997999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114925147187262389265330665 86193860390446791948997999)
  ·
    refine ⟨129290790585670187923496999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86193860390446791948997999 129290790585670187923496999)
    ·
      refine ⟨193936185878505281885245499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129290790585670187923496999 193936185878505281885245499)
      ·
        refine ⟨290904278817757922827868249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193936185878505281885245499 290904278817757922827868249)
        ·
          refine ⟨218178209113318442120901187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290904278817757922827868249 218178209113318442120901187)
          ·
            refine ⟨327267313669977663181351781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218178209113318442120901187 327267313669977663181351781)
            ·
              refine ⟨61362621313120811846503459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327267313669977663181351781 61362621313120811846503459)
              ·
                refine ⟨92043931969681217769755189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61362621313120811846503459 92043931969681217769755189)
                ·
                  refine ⟨8629118622157614165914549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92043931969681217769755189 8629118622157614165914549)
                  ·
                    refine ⟨808979870827276328054489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8629118622157614165914549 808979870827276328054489)
                    ·
                      rfl

theorem cell23_4726448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_4726448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726448 prefixEnd_4726448 := by exact prefixLift 4726448
  have htrace : WordTrace (prefixWord ++ tailWord_4726448) baseStart_4726448 baseEnd_4726448 := by
    simpa [prefixWord, tailWord_4726448, baseEnd_4726448] using wordTrace_append hprefix tailTrace_4726448
  have hstable : (prefixWord ++ tailWord_4726448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726448).length < 2 ^ (prefixWord ++ tailWord_4726448).sum := by decide
  have hdescent : baseEnd_4726448 < baseStart_4726448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726472 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_4726472 : Nat := 118140960795 + 4726472 * 2 ^ 59
def prefixEnd_4726472 : Nat := 4983230072969 + 3 ^ 40 * 4726472 * 2
def baseEnd_4726472 : Nat := 2426951936017536890263357

theorem tailTrace_4726472 : CollatzResearch.WordTrace tailWord_4726472 prefixEnd_4726472 2426951936017536890263357 := by
  unfold tailWord_4726472
  simp only [CollatzResearch.WordTrace]
  refine ⟨86194298066403317998434835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114925730755204423997913113 86194298066403317998434835)
  ·
    refine ⟨129291447099604976997652253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86194298066403317998434835 129291447099604976997652253)
    ·
      refine ⟨48484292662351866374119595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129291447099604976997652253 48484292662351866374119595)
      ·
        refine ⟨72726438993527799561179393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48484292662351866374119595 72726438993527799561179393)
        ·
          refine ⟨54544829245145849670884545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72726438993527799561179393 54544829245145849670884545)
          ·
            refine ⟨40908621933859387253163409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54544829245145849670884545 40908621933859387253163409)
            ·
              refine ⟨30681466450394540439872557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40908621933859387253163409 30681466450394540439872557)
              ·
                refine ⟨11505549918897952664952209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30681466450394540439872557 11505549918897952664952209)
                ·
                  refine ⟨8629162439173464498714157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11505549918897952664952209 8629162439173464498714157)
                  ·
                    refine ⟨3235935914690049187017809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8629162439173464498714157 3235935914690049187017809)
                    ·
                      refine ⟨2426951936017536890263357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235935914690049187017809 2426951936017536890263357)
                      ·
                        rfl

theorem cell23_4726472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_4726472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726472 prefixEnd_4726472 := by exact prefixLift 4726472
  have htrace : WordTrace (prefixWord ++ tailWord_4726472) baseStart_4726472 baseEnd_4726472 := by
    simpa [prefixWord, tailWord_4726472, baseEnd_4726472] using wordTrace_append hprefix tailTrace_4726472
  have hstable : (prefixWord ++ tailWord_4726472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726472).length < 2 ^ (prefixWord ++ tailWord_4726472).sum := by decide
  have hdescent : baseEnd_4726472 < baseStart_4726472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726482 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_4726482 : Nat := 118140960795 + 4726482 * 2 ^ 59
def prefixEnd_4726482 : Nat := 4983230072969 + 3 ^ 40 * 4726482 * 2
def baseEnd_4726482 : Nat := 808985690274693950379437

theorem tailTrace_4726482 : CollatzResearch.WordTrace tailWord_4726482 prefixEnd_4726482 808985690274693950379437 := by
  unfold tailWord_4726482
  simp only [CollatzResearch.WordTrace]
  refine ⟨43097240215692601926183425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114925973908513605136489133 43097240215692601926183425)
  ·
    refine ⟨32322930161769451444637569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43097240215692601926183425 32322930161769451444637569)
    ·
      refine ⟨24242197621327088583478177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32322930161769451444637569 24242197621327088583478177)
      ·
        refine ⟨18181648215995316437608633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24242197621327088583478177 18181648215995316437608633)
        ·
          refine ⟨13636236161996487328206475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18181648215995316437608633 13636236161996487328206475)
          ·
            refine ⟨20454354242994730992309713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13636236161996487328206475 20454354242994730992309713)
            ·
              refine ⟨15340765682246048244232285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20454354242994730992309713 15340765682246048244232285)
              ·
                refine ⟨5752787130842268091587107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15340765682246048244232285 5752787130842268091587107)
                ·
                  refine ⟨8629180696263402137380661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5752787130842268091587107 8629180696263402137380661)
                  ·
                    refine ⟨808985690274693950379437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8629180696263402137380661 808985690274693950379437)
                    ·
                      rfl

theorem cell23_4726482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_4726482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726482 prefixEnd_4726482 := by exact prefixLift 4726482
  have htrace : WordTrace (prefixWord ++ tailWord_4726482) baseStart_4726482 baseEnd_4726482 := by
    simpa [prefixWord, tailWord_4726482, baseEnd_4726482] using wordTrace_append hprefix tailTrace_4726482
  have hstable : (prefixWord ++ tailWord_4726482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726482).length < 2 ^ (prefixWord ++ tailWord_4726482).sum := by decide
  have hdescent : baseEnd_4726482 < baseStart_4726482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726495 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 4, 4]
def baseStart_4726495 : Nat := 118140960795 + 4726495 * 2 ^ 59
def prefixEnd_4726495 : Nat := 4983230072969 + 3 ^ 40 * 4726495 * 2
def baseEnd_4726495 : Nat := 808987915357530100091917

theorem tailTrace_4726495 : CollatzResearch.WordTrace tailWord_4726495 prefixEnd_4726495 808987915357530100091917 := by
  unfold tailWord_4726495
  simp only [CollatzResearch.WordTrace]
  refine ⟨172389435011723310924956939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114926290007815540616637959 172389435011723310924956939)
  ·
    refine ⟨258584152517584966387435409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172389435011723310924956939 258584152517584966387435409)
    ·
      refine ⟨193938114388188724790576557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258584152517584966387435409 193938114388188724790576557)
      ·
        refine ⟨72726792895570771796466209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193938114388188724790576557 72726792895570771796466209)
        ·
          refine ⟨54545094671678078847349657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72726792895570771796466209 54545094671678078847349657)
          ·
            refine ⟨40908821003758559135512243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54545094671678078847349657 40908821003758559135512243)
            ·
              refine ⟨61363231505637838703268365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40908821003758559135512243 61363231505637838703268365)
              ·
                refine ⟨23011211814614189513725637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61363231505637838703268365 23011211814614189513725637)
                ·
                  refine ⟨4314602215240160533823557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23011211814614189513725637 4314602215240160533823557)
                  ·
                    refine ⟨808987915357530100091917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4314602215240160533823557 808987915357530100091917)
                    ·
                      rfl

theorem cell23_4726495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 4].length) (baseStart_4726495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726495 prefixEnd_4726495 := by exact prefixLift 4726495
  have htrace : WordTrace (prefixWord ++ tailWord_4726495) baseStart_4726495 baseEnd_4726495 := by
    simpa [prefixWord, tailWord_4726495, baseEnd_4726495] using wordTrace_append hprefix tailTrace_4726495
  have hstable : (prefixWord ++ tailWord_4726495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726495).length < 2 ^ (prefixWord ++ tailWord_4726495).sum := by decide
  have hdescent : baseEnd_4726495 < baseStart_4726495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726505 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 3]
def baseStart_4726505 : Nat := 118140960795 + 4726505 * 2 ^ 59
def prefixEnd_4726505 : Nat := 4983230072969 + 3 ^ 40 * 4726505 * 2
def baseEnd_4726505 : Nat := 2426968880879135261150705

theorem tailTrace_4726505 : CollatzResearch.WordTrace tailWord_4726505 prefixEnd_4726505 2426968880879135261150705 := by
  unfold tailWord_4726505
  simp only [CollatzResearch.WordTrace]
  refine ⟨172389799741687082632820969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114926533161124721755213979 172389799741687082632820969)
  ·
    refine ⟨129292349806265311974615727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172389799741687082632820969 129292349806265311974615727)
    ·
      refine ⟨193938524709397967961923591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129292349806265311974615727 193938524709397967961923591)
      ·
        refine ⟨290907787064096951942885387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193938524709397967961923591 290907787064096951942885387)
        ·
          refine ⟨436361680596145427914328081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290907787064096951942885387 436361680596145427914328081)
          ·
            refine ⟨327271260447109070935746061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436361680596145427914328081 327271260447109070935746061)
            ·
              refine ⟨122726722667665901600904773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327271260447109070935746061 122726722667665901600904773)
              ·
                refine ⟨23011260500187356550169645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122726722667665901600904773 23011260500187356550169645)
                ·
                  refine ⟨8629222687570258706313617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23011260500187356550169645 8629222687570258706313617)
                  ·
                    refine ⟨6471917015677694029735213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8629222687570258706313617 6471917015677694029735213)
                    ·
                      refine ⟨2426968880879135261150705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6471917015677694029735213 2426968880879135261150705)
                      ·
                        rfl

theorem cell23_4726505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_4726505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726505 prefixEnd_4726505 := by exact prefixLift 4726505
  have htrace : WordTrace (prefixWord ++ tailWord_4726505) baseStart_4726505 baseEnd_4726505 := by
    simpa [prefixWord, tailWord_4726505, baseEnd_4726505] using wordTrace_append hprefix tailTrace_4726505
  have hstable : (prefixWord ++ tailWord_4726505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726505).length < 2 ^ (prefixWord ++ tailWord_4726505).sum := by decide
  have hdescent : baseEnd_4726505 < baseStart_4726505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726508 : List Nat := [2, 2, 1, 1, 2, 2, 3, 10]
def baseStart_4726508 : Nat := 118140960795 + 4726508 * 2 ^ 59
def prefixEnd_4726508 : Nat := 4983230072969 + 3 ^ 40 * 4726508 * 2
def baseEnd_4726508 : Nat := 89887793382262916644933

theorem tailTrace_4726508 : CollatzResearch.WordTrace tailWord_4726508 prefixEnd_4726508 89887793382262916644933 := by
  unfold tailWord_4726508
  simp only [CollatzResearch.WordTrace]
  refine ⟨86194954580338107072590089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114926606107117476096786785 86194954580338107072590089)
  ·
    refine ⟨64646215935253580304442567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86194954580338107072590089 64646215935253580304442567)
    ·
      refine ⟨96969323902880370456663851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64646215935253580304442567 96969323902880370456663851)
      ·
        refine ⟨145453985854320555684995777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96969323902880370456663851 145453985854320555684995777)
        ·
          refine ⟨109090489390740416763746833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145453985854320555684995777 109090489390740416763746833)
          ·
            refine ⟨81817867043055312572810125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109090489390740416763746833 81817867043055312572810125)
            ·
              refine ⟨30681700141145742214803797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81817867043055312572810125 30681700141145742214803797)
              ·
                refine ⟨89887793382262916644933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30681700141145742214803797 89887793382262916644933)
                ·
                  rfl

theorem cell23_4726508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 10].length) (baseStart_4726508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726508 prefixEnd_4726508 := by exact prefixLift 4726508
  have htrace : WordTrace (prefixWord ++ tailWord_4726508) baseStart_4726508 baseEnd_4726508 := by
    simpa [prefixWord, tailWord_4726508, baseEnd_4726508] using wordTrace_append hprefix tailTrace_4726508
  have hstable : (prefixWord ++ tailWord_4726508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726508).length < 2 ^ (prefixWord ++ tailWord_4726508).sum := by decide
  have hdescent : baseEnd_4726508 < baseStart_4726508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726516 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4726516 : Nat := 118140960795 + 4726516 * 2 ^ 59
def prefixEnd_4726516 : Nat := 4983230072969 + 3 ^ 40 * 4726516 * 2
def baseEnd_4726516 : Nat := 808991509722111572704385

theorem tailTrace_4726516 : CollatzResearch.WordTrace tailWord_4726516 prefixEnd_4726516 808991509722111572704385 := by
  unfold tailWord_4726516
  simp only [CollatzResearch.WordTrace]
  refine ⟨86195100472323615755735701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114926800629764821007647601 86195100472323615755735701)
  ·
    refine ⟨4040395334640169488550111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86195100472323615755735701 4040395334640169488550111)
    ·
      refine ⟨6060593001960254232825167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4040395334640169488550111 6060593001960254232825167)
      ·
        refine ⟨9090889502940381349237751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6060593001960254232825167 9090889502940381349237751)
        ·
          refine ⟨13636334254410572023856627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9090889502940381349237751 13636334254410572023856627)
          ·
            refine ⟨20454501381615858035784941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13636334254410572023856627 20454501381615858035784941)
            ·
              refine ⟨7670438018105946763419353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20454501381615858035784941 7670438018105946763419353)
              ·
                refine ⟨5752828513579460072564515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7670438018105946763419353 5752828513579460072564515)
                ·
                  refine ⟨8629242770369190108846773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5752828513579460072564515 8629242770369190108846773)
                  ·
                    refine ⟨808991509722111572704385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8629242770369190108846773 808991509722111572704385)
                    ·
                      rfl

theorem cell23_4726516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4726516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726516 prefixEnd_4726516 := by exact prefixLift 4726516
  have htrace : WordTrace (prefixWord ++ tailWord_4726516) baseStart_4726516 baseEnd_4726516 := by
    simpa [prefixWord, tailWord_4726516, baseEnd_4726516] using wordTrace_append hprefix tailTrace_4726516
  have hstable : (prefixWord ++ tailWord_4726516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726516).length < 2 ^ (prefixWord ++ tailWord_4726516).sum := by decide
  have hdescent : baseEnd_4726516 < baseStart_4726516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726528 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_4726528 : Nat := 118140960795 + 4726528 * 2 ^ 59
def prefixEnd_4726528 : Nat := 4983230072969 + 3 ^ 40 * 4726528 * 2
def baseEnd_4726528 : Nat := 2426980690934188671163099

theorem tailTrace_4726528 : CollatzResearch.WordTrace tailWord_4726528 prefixEnd_4726528 2426980690934188671163099 := by
  unfold tailWord_4726528
  simp only [CollatzResearch.WordTrace]
  refine ⟨86195319310301878780454119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114927092413735838373938825 86195319310301878780454119)
  ·
    refine ⟨129292978965452818170681179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86195319310301878780454119 129292978965452818170681179)
    ·
      refine ⟨193939468448179227256021769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129292978965452818170681179 193939468448179227256021769)
      ·
        refine ⟨145454601336134420442016327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193939468448179227256021769 145454601336134420442016327)
        ·
          refine ⟨218181902004201630663024491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145454601336134420442016327 218181902004201630663024491)
          ·
            refine ⟨327272853006302445994536737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218181902004201630663024491 327272853006302445994536737)
            ·
              refine ⟨245454639754726834495902553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327272853006302445994536737 245454639754726834495902553)
              ·
                refine ⟨184090979816045125871926915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245454639754726834495902553 184090979816045125871926915)
                ·
                  refine ⟨276136469724067688807890373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184090979816045125871926915 276136469724067688807890373)
                  ·
                    refine ⟨51775588073262691651479445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 276136469724067688807890373 51775588073262691651479445)
                    ·
                      refine ⟨2426980690934188671163099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51775588073262691651479445 2426980690934188671163099)
                      ·
                        rfl

theorem cell23_4726528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_4726528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726528 prefixEnd_4726528 := by exact prefixLift 4726528
  have htrace : WordTrace (prefixWord ++ tailWord_4726528) baseStart_4726528 baseEnd_4726528 := by
    simpa [prefixWord, tailWord_4726528, baseEnd_4726528] using wordTrace_append hprefix tailTrace_4726528
  have hstable : (prefixWord ++ tailWord_4726528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726528).length < 2 ^ (prefixWord ++ tailWord_4726528).sum := by decide
  have hdescent : baseEnd_4726528 < baseStart_4726528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726532 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4726532 : Nat := 118140960795 + 4726532 * 2 ^ 59
def prefixEnd_4726532 : Nat := 4983230072969 + 3 ^ 40 * 4726532 * 2
def baseEnd_4726532 : Nat := 2426982744856806655513081

theorem tailTrace_4726532 : CollatzResearch.WordTrace tailWord_4726532 prefixEnd_4726532 2426982744856806655513081 := by
  unfold tailWord_4726532
  simp only [CollatzResearch.WordTrace]
  refine ⟨86195392256294633122026925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114927189675059510829369233 86195392256294633122026925)
  ·
    refine ⟨32323272096110487420760097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86195392256294633122026925 32323272096110487420760097)
    ·
      refine ⟨24242454072082865565570073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32323272096110487420760097 24242454072082865565570073)
      ·
        refine ⟨18181840554062149174177555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24242454072082865565570073 18181840554062149174177555)
        ·
          refine ⟨27272760831093223761266333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18181840554062149174177555 27272760831093223761266333)
          ·
            refine ⟨10227285311659958910474875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27272760831093223761266333 10227285311659958910474875)
            ·
              refine ⟨15340927967489938365712313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10227285311659958910474875 15340927967489938365712313)
              ·
                refine ⟨11505695975617453774284235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15340927967489938365712313 11505695975617453774284235)
                ·
                  refine ⟨17258543963426180661426353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11505695975617453774284235 17258543963426180661426353)
                  ·
                    refine ⟨12943907972569635496069765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17258543963426180661426353 12943907972569635496069765)
                    ·
                      refine ⟨2426982744856806655513081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12943907972569635496069765 2426982744856806655513081)
                      ·
                        rfl

theorem cell23_4726532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4726532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726532 prefixEnd_4726532 := by exact prefixLift 4726532
  have htrace : WordTrace (prefixWord ++ tailWord_4726532) baseStart_4726532 baseEnd_4726532 := by
    simpa [prefixWord, tailWord_4726532, baseEnd_4726532] using wordTrace_append hprefix tailTrace_4726532
  have hstable : (prefixWord ++ tailWord_4726532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726532).length < 2 ^ (prefixWord ++ tailWord_4726532).sum := by decide
  have hdescent : baseEnd_4726532 < baseStart_4726532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726536 : List Nat := [2, 1, 3, 2, 2, 1, 2, 5, 1, 2, 2]
def baseStart_4726536 : Nat := 118140960795 + 4726536 * 2 ^ 59
def prefixEnd_4726536 : Nat := 4983230072969 + 3 ^ 40 * 4726536 * 2
def baseEnd_4726536 : Nat := 2426984798779424639863063

theorem tailTrace_4726536 : CollatzResearch.WordTrace tailWord_4726536 prefixEnd_4726536 2426984798779424639863063 := by
  unfold tailWord_4726536
  simp only [CollatzResearch.WordTrace]
  refine ⟨86195465202287387463599731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114927286936383183284799641 86195465202287387463599731)
  ·
    refine ⟨129293197803431081195399597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86195465202287387463599731 129293197803431081195399597)
    ·
      refine ⟨48484949176286655448274849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129293197803431081195399597 48484949176286655448274849)
      ·
        refine ⟨36363711882214991586206137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48484949176286655448274849 36363711882214991586206137)
        ·
          refine ⟨27272783911661243689654603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36363711882214991586206137 27272783911661243689654603)
          ·
            refine ⟨40909175867491865534481905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27272783911661243689654603 40909175867491865534481905)
            ·
              refine ⟨30681881900618899150861429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40909175867491865534481905 30681881900618899150861429)
              ·
                refine ⟨2876426428183021795393259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30681881900618899150861429 2876426428183021795393259)
                ·
                  refine ⟨4314639642274532693089889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876426428183021795393259 4314639642274532693089889)
                  ·
                    refine ⟨3235979731705899519817417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4314639642274532693089889 3235979731705899519817417)
                    ·
                      refine ⟨2426984798779424639863063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235979731705899519817417 2426984798779424639863063)
                      ·
                        rfl

theorem cell23_4726536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_4726536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726536 prefixEnd_4726536 := by exact prefixLift 4726536
  have htrace : WordTrace (prefixWord ++ tailWord_4726536) baseStart_4726536 baseEnd_4726536 := by
    simpa [prefixWord, tailWord_4726536, baseEnd_4726536] using wordTrace_append hprefix tailTrace_4726536
  have hstable : (prefixWord ++ tailWord_4726536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726536).length < 2 ^ (prefixWord ++ tailWord_4726536).sum := by decide
  have hdescent : baseEnd_4726536 < baseStart_4726536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726546 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4726546 : Nat := 118140960795 + 4726546 * 2 ^ 59
def prefixEnd_4726546 : Nat := 4983230072969 + 3 ^ 40 * 4726546 * 2
def baseEnd_4726546 : Nat := 808996644528656533579339

theorem tailTrace_4726546 : CollatzResearch.WordTrace tailWord_4726546 prefixEnd_4726546 808996644528656533579339 := by
  unfold tailWord_4726546
  simp only [CollatzResearch.WordTrace]
  refine ⟨43097823783634636658765873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114927530089692364423375661 43097823783634636658765873)
  ·
    refine ⟨32323367837725977494074405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43097823783634636658765873 32323367837725977494074405)
    ·
      refine ⟨6060631469573620780138951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32323367837725977494074405 6060631469573620780138951)
      ·
        refine ⟨9090947204360431170208427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6060631469573620780138951 9090947204360431170208427)
        ·
          refine ⟨13636420806540646755312641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9090947204360431170208427 13636420806540646755312641)
          ·
            refine ⟨10227315604905485066484481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13636420806540646755312641 10227315604905485066484481)
            ·
              refine ⟨7670486703679113799863361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10227315604905485066484481 7670486703679113799863361)
              ·
                refine ⟨5752865027759335349897521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7670486703679113799863361 5752865027759335349897521)
                ·
                  refine ⟨4314648770819501512423141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5752865027759335349897521 4314648770819501512423141)
                  ·
                    refine ⟨808996644528656533579339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4314648770819501512423141 808996644528656533579339)
                    ·
                      rfl

theorem cell23_4726546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4726546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726546 prefixEnd_4726546 := by exact prefixLift 4726546
  have htrace : WordTrace (prefixWord ++ tailWord_4726546) baseStart_4726546 baseEnd_4726546 := by
    simpa [prefixWord, tailWord_4726546, baseEnd_4726546] using wordTrace_append hprefix tailTrace_4726546
  have hstable : (prefixWord ++ tailWord_4726546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726546).length < 2 ^ (prefixWord ++ tailWord_4726546).sum := by decide
  have hdescent : baseEnd_4726546 < baseStart_4726546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726552 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 4, 1, 3]
def baseStart_4726552 : Nat := 118140960795 + 4726552 * 2 ^ 59
def prefixEnd_4726552 : Nat := 4983230072969 + 3 ^ 40 * 4726552 * 2
def baseEnd_4726552 : Nat := 2426993014469896577262989

theorem tailTrace_4726552 : CollatzResearch.WordTrace tailWord_4726552 prefixEnd_4726552 2426993014469896577262989 := by
  unfold tailWord_4726552
  simp only [CollatzResearch.WordTrace]
  refine ⟨86195756986258404829890955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114927675981677873106521273 86195756986258404829890955)
  ·
    refine ⟨129293635479387607244836433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86195756986258404829890955 129293635479387607244836433)
    ·
      refine ⟨96970226609540705433627325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129293635479387607244836433 96970226609540705433627325)
      ·
        refine ⟨36363834978577764537610247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96970226609540705433627325 36363834978577764537610247)
        ·
          refine ⟨54545752467866646806415371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36363834978577764537610247 54545752467866646806415371)
          ·
            refine ⟨81818628701799970209623057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54545752467866646806415371 81818628701799970209623057)
            ·
              refine ⟨61363971526349977657217293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81818628701799970209623057 61363971526349977657217293)
              ·
                refine ⟨23011489322381241621456485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61363971526349977657217293 23011489322381241621456485)
                ·
                  refine ⟨4314654247946482804023091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23011489322381241621456485 4314654247946482804023091)
                  ·
                    refine ⟨6471981371919724206034637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4314654247946482804023091 6471981371919724206034637)
                    ·
                      refine ⟨2426993014469896577262989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6471981371919724206034637 2426993014469896577262989)
                      ·
                        rfl

theorem cell23_4726552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_4726552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726552 prefixEnd_4726552 := by exact prefixLift 4726552
  have htrace : WordTrace (prefixWord ++ tailWord_4726552) baseStart_4726552 baseEnd_4726552 := by
    simpa [prefixWord, tailWord_4726552, baseEnd_4726552] using wordTrace_append hprefix tailTrace_4726552
  have hstable : (prefixWord ++ tailWord_4726552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726552).length < 2 ^ (prefixWord ++ tailWord_4726552).sum := by decide
  have hdescent : baseEnd_4726552 < baseStart_4726552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726626 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_4726626 : Nat := 118140960795 + 4726626 * 2 ^ 59
def prefixEnd_4726626 : Nat := 4983230072969 + 3 ^ 40 * 4726626 * 2
def baseEnd_4726626 : Nat := 2427031012038329287737649

theorem tailTrace_4726626 : CollatzResearch.WordTrace tailWord_4726626 prefixEnd_4726626 2427031012038329287737649 := by
  unfold tailWord_4726626
  simp only [CollatzResearch.WordTrace]
  refine ⟨43098553243562180074493933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114929475316165813531983821 43098553243562180074493933)
  ·
    refine ⟨16161957466335817527935225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43098553243562180074493933 16161957466335817527935225)
    ·
      refine ⟨12121468099751863145951419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16161957466335817527935225 12121468099751863145951419)
      ·
        refine ⟨18182202149627794718927129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12121468099751863145951419 18182202149627794718927129)
        ·
          refine ⟨13636651612220846039195347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18182202149627794718927129 13636651612220846039195347)
          ·
            refine ⟨20454977418331269058793021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13636651612220846039195347 20454977418331269058793021)
            ·
              refine ⟨7670616531874225897047383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20454977418331269058793021 7670616531874225897047383)
              ·
                refine ⟨11505924797811338845571075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7670616531874225897047383 11505924797811338845571075)
                ·
                  refine ⟨17258887196717008268356613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11505924797811338845571075 17258887196717008268356613)
                  ·
                    refine ⟨3236041349384439050316865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17258887196717008268356613 3236041349384439050316865)
                    ·
                      refine ⟨2427031012038329287737649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3236041349384439050316865 2427031012038329287737649)
                      ·
                        rfl

theorem cell23_4726626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_4726626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726626 prefixEnd_4726626 := by exact prefixLift 4726626
  have htrace : WordTrace (prefixWord ++ tailWord_4726626) baseStart_4726626 baseEnd_4726626 := by
    simpa [prefixWord, tailWord_4726626, baseEnd_4726626] using wordTrace_append hprefix tailTrace_4726626
  have hstable : (prefixWord ++ tailWord_4726626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726626).length < 2 ^ (prefixWord ++ tailWord_4726626).sum := by decide
  have hdescent : baseEnd_4726626 < baseStart_4726626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726652 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 3, 7, 2]
def baseStart_4726652 : Nat := 118140960795 + 4726652 * 2 ^ 59
def prefixEnd_4726652 : Nat := 4983230072969 + 3 ^ 40 * 4726652 * 2
def baseEnd_4726652 : Nat := 2427044362535346186012529

theorem tailTrace_4726652 : CollatzResearch.WordTrace tailWord_4726652 prefixEnd_4726652 2427044362535346186012529 := by
  unfold tailWord_4726652
  simp only [CollatzResearch.WordTrace]
  refine ⟨86197580636077263369211105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114930107514769684492281473 86197580636077263369211105)
  ·
    refine ⟨64648185477057947526908329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86197580636077263369211105 64648185477057947526908329)
    ·
      refine ⟨48486139107793460645181247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64648185477057947526908329 48486139107793460645181247)
      ·
        refine ⟨72729208661690190967771871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48486139107793460645181247 72729208661690190967771871)
        ·
          refine ⟨109093812992535286451657807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72729208661690190967771871 109093812992535286451657807)
          ·
            refine ⟨163640719488802929677486711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109093812992535286451657807 163640719488802929677486711)
            ·
              refine ⟨245461079233204394516230067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163640719488802929677486711 245461079233204394516230067)
              ·
                refine ⟨368191618849806591774345101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245461079233204394516230067 368191618849806591774345101)
                ·
                  refine ⟨138071857068677471915379413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368191618849806591774345101 138071857068677471915379413)
                  ·
                    refine ⟨3236059150047128248016705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 138071857068677471915379413 3236059150047128248016705)
                    ·
                      refine ⟨2427044362535346186012529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3236059150047128248016705 2427044362535346186012529)
                      ·
                        rfl

theorem cell23_4726652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_4726652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726652 prefixEnd_4726652 := by exact prefixLift 4726652
  have htrace : WordTrace (prefixWord ++ tailWord_4726652) baseStart_4726652 baseEnd_4726652 := by
    simpa [prefixWord, tailWord_4726652, baseEnd_4726652] using wordTrace_append hprefix tailTrace_4726652
  have hstable : (prefixWord ++ tailWord_4726652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726652).length < 2 ^ (prefixWord ++ tailWord_4726652).sum := by decide
  have hdescent : baseEnd_4726652 < baseStart_4726652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726655 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_4726655 : Nat := 118140960795 + 4726655 * 2 ^ 59
def prefixEnd_4726655 : Nat := 4983230072969 + 3 ^ 40 * 4726655 * 2
def baseEnd_4726655 : Nat := 2427045902977309674275015

theorem tailTrace_4726655 : CollatzResearch.WordTrace tailWord_4726655 prefixEnd_4726655 2427045902977309674275015 := by
  unfold tailWord_4726655
  simp only [CollatzResearch.WordTrace]
  refine ⟨172395270691143658250781419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114930180460762438833854279 172395270691143658250781419)
  ·
    refine ⟨258592906036715487376172129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172395270691143658250781419 258592906036715487376172129)
    ·
      refine ⟨193944679527536615532129097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258592906036715487376172129 193944679527536615532129097)
      ·
        refine ⟨145458509645652461649096823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193944679527536615532129097 145458509645652461649096823)
        ·
          refine ⟨218187764468478692473645235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145458509645652461649096823 218187764468478692473645235)
          ·
            refine ⟨327281646702718038710467853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218187764468478692473645235 327281646702718038710467853)
            ·
              refine ⟨122730617513519264516425445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327281646702718038710467853 122730617513519264516425445)
              ·
                refine ⟨23011990783784862096829771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122730617513519264516425445 23011990783784862096829771)
                ·
                  refine ⟨34517986175677293145244657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23011990783784862096829771 34517986175677293145244657)
                  ·
                    refine ⟨25888489631757969858933493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34517986175677293145244657 25888489631757969858933493)
                    ·
                      refine ⟨2427045902977309674275015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25888489631757969858933493 2427045902977309674275015)
                      ·
                        rfl

theorem cell23_4726655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_4726655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726655 prefixEnd_4726655 := by exact prefixLift 4726655
  have htrace : WordTrace (prefixWord ++ tailWord_4726655) baseStart_4726655 baseEnd_4726655 := by
    simpa [prefixWord, tailWord_4726655, baseEnd_4726655] using wordTrace_append hprefix tailTrace_4726655
  have hstable : (prefixWord ++ tailWord_4726655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726655).length < 2 ^ (prefixWord ++ tailWord_4726655).sum := by decide
  have hdescent : baseEnd_4726655 < baseStart_4726655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726666 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 7]
def baseStart_4726666 : Nat := 118140960795 + 4726666 * 2 ^ 59
def prefixEnd_4726666 : Nat := 4983230072969 + 3 ^ 40 * 4726666 * 2
def baseEnd_4726666 : Nat := 269672394584945459026385

theorem tailTrace_4726666 : CollatzResearch.WordTrace tailWord_4726666 prefixEnd_4726666 269672394584945459026385 := by
  unfold tailWord_4726666
  simp only [CollatzResearch.WordTrace]
  refine ⟨43098917973525951782357963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114930447929402538086287901 43098917973525951782357963)
  ·
    refine ⟨64648376960288927673536945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43098917973525951782357963 64648376960288927673536945)
    ·
      refine ⟨48486282720216695755152709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64648376960288927673536945 48486282720216695755152709)
      ·
        refine ⟨9091178010040630454091133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48486282720216695755152709 9091178010040630454091133)
        ·
          refine ⟨3409191753765236420284175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9091178010040630454091133 3409191753765236420284175)
          ·
            refine ⟨5113787630647854630426263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409191753765236420284175 5113787630647854630426263)
            ·
              refine ⟨7670681445971781945639395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5113787630647854630426263 7670681445971781945639395)
              ·
                refine ⟨11506022168957672918459093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7670681445971781945639395 11506022168957672918459093)
                ·
                  refine ⟨269672394584945459026385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11506022168957672918459093 269672394584945459026385)
                  ·
                    rfl

theorem cell23_4726666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_4726666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726666 prefixEnd_4726666 := by exact prefixLift 4726666
  have htrace : WordTrace (prefixWord ++ tailWord_4726666) baseStart_4726666 baseEnd_4726666 := by
    simpa [prefixWord, tailWord_4726666, baseEnd_4726666] using wordTrace_append hprefix tailTrace_4726666
  have hstable : (prefixWord ++ tailWord_4726666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726666).length < 2 ^ (prefixWord ++ tailWord_4726666).sum := by decide
  have hdescent : baseEnd_4726666 < baseStart_4726666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726817 : List Nat := [1, 2, 3, 2, 5, 1, 1, 3, 1, 1, 3]
def baseStart_4726817 : Nat := 118140960795 + 4726817 * 2 ^ 59
def prefixEnd_4726817 : Nat := 4983230072969 + 3 ^ 40 * 4726817 * 2
def baseEnd_4726817 : Nat := 2427129086843338040449271

theorem tailTrace_4726817 : CollatzResearch.WordTrace tailWord_4726817 prefixEnd_4726817 2427129086843338040449271 := by
  unfold tailWord_4726817
  simp only [CollatzResearch.WordTrace]
  refine ⟨172401179316556759918178705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114934119544371173278785803 172401179316556759918178705)
  ·
    refine ⟨129300884487417569938634029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172401179316556759918178705 129300884487417569938634029)
    ·
      refine ⟨48487831682781588726987761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129300884487417569938634029 48487831682781588726987761)
      ·
        refine ⟨36365873762086191545240821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48487831682781588726987761 36365873762086191545240821)
        ·
          refine ⟨3409300665195580457366327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36365873762086191545240821 3409300665195580457366327)
          ·
            refine ⟨5113950997793370686049491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409300665195580457366327 5113950997793370686049491)
            ·
              refine ⟨7670926496690056029074237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5113950997793370686049491 7670926496690056029074237)
              ·
                refine ⟨2876597436258771010902839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7670926496690056029074237 2876597436258771010902839)
                ·
                  refine ⟨4314896154388156516354259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876597436258771010902839 4314896154388156516354259)
                  ·
                    refine ⟨6472344231582234774531389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4314896154388156516354259 6472344231582234774531389)
                    ·
                      refine ⟨2427129086843338040449271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6472344231582234774531389 2427129086843338040449271)
                      ·
                        rfl

theorem cell23_4726817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_4726817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726817 prefixEnd_4726817 := by exact prefixLift 4726817
  have htrace : WordTrace (prefixWord ++ tailWord_4726817) baseStart_4726817 baseEnd_4726817 := by
    simpa [prefixWord, tailWord_4726817, baseEnd_4726817] using wordTrace_append hprefix tailTrace_4726817
  have hstable : (prefixWord ++ tailWord_4726817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726817).length < 2 ^ (prefixWord ++ tailWord_4726817).sum := by decide
  have hdescent : baseEnd_4726817 < baseStart_4726817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726826 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_4726826 : Nat := 118140960795 + 4726826 * 2 ^ 59
def prefixEnd_4726826 : Nat := 4983230072969 + 3 ^ 40 * 4726826 * 2
def baseEnd_4726826 : Nat := 2427133708169228505236729

theorem tailTrace_4726826 : CollatzResearch.WordTrace tailWord_4726826 prefixEnd_4726826 2427133708169228505236729 := by
  unfold tailWord_4726826
  simp only [CollatzResearch.WordTrace]
  refine ⟨43100376893381038613814083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114934338382349436303504221 43100376893381038613814083)
  ·
    refine ⟨64650565340071557920721125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43100376893381038613814083 64650565340071557920721125)
    ·
      refine ⟨12121981001263417110135211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64650565340071557920721125 12121981001263417110135211)
      ·
        refine ⟨18182971501895125665202817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12121981001263417110135211 18182971501895125665202817)
        ·
          refine ⟨13637228626421344248902113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18182971501895125665202817 13637228626421344248902113)
          ·
            refine ⟨10227921469816008186676585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13637228626421344248902113 10227921469816008186676585)
            ·
              refine ⟨7670941102362006140007439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10227921469816008186676585 7670941102362006140007439)
              ·
                refine ⟨11506411653543009210011159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7670941102362006140007439 11506411653543009210011159)
                ·
                  refine ⟨17259617480314513815016739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11506411653543009210011159 17259617480314513815016739)
                  ·
                    refine ⟨25889426220471770722525109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17259617480314513815016739 25889426220471770722525109)
                    ·
                      refine ⟨2427133708169228505236729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25889426220471770722525109 2427133708169228505236729)
                      ·
                        rfl

theorem cell23_4726826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_4726826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726826 prefixEnd_4726826 := by exact prefixLift 4726826
  have htrace : WordTrace (prefixWord ++ tailWord_4726826) baseStart_4726826 baseEnd_4726826 := by
    simpa [prefixWord, tailWord_4726826, baseEnd_4726826] using wordTrace_append hprefix tailTrace_4726826
  have hstable : (prefixWord ++ tailWord_4726826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726826).length < 2 ^ (prefixWord ++ tailWord_4726826).sum := by decide
  have hdescent : baseEnd_4726826 < baseStart_4726826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726840 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 3, 2, 2]
def baseStart_4726840 : Nat := 118140960795 + 4726840 * 2 ^ 59
def prefixEnd_4726840 : Nat := 4983230072969 + 3 ^ 40 * 4726840 * 2
def baseEnd_4726840 : Nat := 2427140896898391450461665

theorem tailTrace_4726840 : CollatzResearch.WordTrace tailWord_4726840 prefixEnd_4726840 2427140896898391450461665 := by
  unfold tailWord_4726840
  simp only [CollatzResearch.WordTrace]
  refine ⟨86201009097736717423132987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114934678796982289897510649 86201009097736717423132987)
  ·
    refine ⟨129301513646605076134699481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86201009097736717423132987 129301513646605076134699481)
    ·
      refine ⟨96976135234953807101024611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129301513646605076134699481 96976135234953807101024611)
      ·
        refine ⟨145464202852430710651536917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96976135234953807101024611 145464202852430710651536917)
        ·
          refine ⟨6818634508707689561790793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145464202852430710651536917 6818634508707689561790793)
          ·
            refine ⟨5113975881530767171343095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6818634508707689561790793 5113975881530767171343095)
            ·
              refine ⟨7670963822296150757014643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5113975881530767171343095 7670963822296150757014643)
              ·
                refine ⟨11506445733444226135521965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7670963822296150757014643 11506445733444226135521965)
                ·
                  refine ⟨4314917150041584800820737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11506445733444226135521965 4314917150041584800820737)
                  ·
                    refine ⟨3236187862531188600615553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4314917150041584800820737 3236187862531188600615553)
                    ·
                      refine ⟨2427140896898391450461665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3236187862531188600615553 2427140896898391450461665)
                      ·
                        rfl

theorem cell23_4726840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_4726840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726840 prefixEnd_4726840 := by exact prefixLift 4726840
  have htrace : WordTrace (prefixWord ++ tailWord_4726840) baseStart_4726840 baseEnd_4726840 := by
    simpa [prefixWord, tailWord_4726840, baseEnd_4726840] using wordTrace_append hprefix tailTrace_4726840
  have hstable : (prefixWord ++ tailWord_4726840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726840).length < 2 ^ (prefixWord ++ tailWord_4726840).sum := by decide
  have hdescent : baseEnd_4726840 < baseStart_4726840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726842 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_4726842 : Nat := 118140960795 + 4726842 * 2 ^ 59
def prefixEnd_4726842 : Nat := 4983230072969 + 3 ^ 40 * 4726842 * 2
def baseEnd_4726842 : Nat := 809047307953233480878885

theorem tailTrace_4726842 : CollatzResearch.WordTrace tailWord_4726842 prefixEnd_4726842 809047307953233480878885 := by
  unfold tailWord_4726842
  simp only [CollatzResearch.WordTrace]
  refine ⟨43100522785366547296959695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114934727427644126125225853 43100522785366547296959695)
  ·
    refine ⟨64650784178049820945439543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43100522785366547296959695 64650784178049820945439543)
    ·
      refine ⟨96976176267074731418159315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64650784178049820945439543 96976176267074731418159315)
      ·
        refine ⟨145464264400612097127238973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96976176267074731418159315 145464264400612097127238973)
        ·
          refine ⟨54549099150229536422714615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145464264400612097127238973 54549099150229536422714615)
          ·
            refine ⟨81823648725344304634071923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54549099150229536422714615 81823648725344304634071923)
            ·
              refine ⟨122735473088016456951107885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81823648725344304634071923 122735473088016456951107885)
              ·
                refine ⟨46025802408006171356665457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122735473088016456951107885 46025802408006171356665457)
                ·
                  refine ⟨34519351806004628517499093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46025802408006171356665457 34519351806004628517499093)
                  ·
                    refine ⟨809047307953233480878885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34519351806004628517499093 809047307953233480878885)
                    ·
                      rfl

theorem cell23_4726842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_4726842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726842 prefixEnd_4726842 := by exact prefixLift 4726842
  have htrace : WordTrace (prefixWord ++ tailWord_4726842) baseStart_4726842 baseEnd_4726842 := by
    simpa [prefixWord, tailWord_4726842, baseEnd_4726842] using wordTrace_append hprefix tailTrace_4726842
  have hstable : (prefixWord ++ tailWord_4726842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726842).length < 2 ^ (prefixWord ++ tailWord_4726842).sum := by decide
  have hdescent : baseEnd_4726842 < baseStart_4726842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726846 : List Nat := [4, 2, 1, 3, 2, 1, 2, 8]
def baseStart_4726846 : Nat := 118140960795 + 4726846 * 2 ^ 59
def prefixEnd_4726846 : Nat := 4983230072969 + 3 ^ 40 * 4726846 * 2
def baseEnd_4726846 : Nat := 89894221399345126925431

theorem tailTrace_4726846 : CollatzResearch.WordTrace tailWord_4726846 prefixEnd_4726846 89894221399345126925431 := by
  unfold tailWord_4726846
  simp only [CollatzResearch.WordTrace]
  refine ⟨21550279629181462233873049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114934824688967798580656261 21550279629181462233873049)
  ·
    refine ⟨16162709721886096675404787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21550279629181462233873049 16162709721886096675404787)
    ·
      refine ⟨24244064582829145013107181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16162709721886096675404787 24244064582829145013107181)
      ·
        refine ⟨9091524218560929379915193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24244064582829145013107181 9091524218560929379915193)
        ·
          refine ⟨6818643163920697034936395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9091524218560929379915193 6818643163920697034936395)
          ·
            refine ⟨10227964745881045552404593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6818643163920697034936395 10227964745881045552404593)
            ·
              refine ⟨7670973559410784164303445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10227964745881045552404593 7670973559410784164303445)
              ·
                refine ⟨89894221399345126925431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7670973559410784164303445 89894221399345126925431)
                ·
                  rfl

theorem cell23_4726846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_4726846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726846 prefixEnd_4726846 := by exact prefixLift 4726846
  have htrace : WordTrace (prefixWord ++ tailWord_4726846) baseStart_4726846 baseEnd_4726846 := by
    simpa [prefixWord, tailWord_4726846, baseEnd_4726846] using wordTrace_append hprefix tailTrace_4726846
  have hstable : (prefixWord ++ tailWord_4726846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726846).length < 2 ^ (prefixWord ++ tailWord_4726846).sum := by decide
  have hdescent : baseEnd_4726846 < baseStart_4726846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726890 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_4726890 : Nat := 118140960795 + 4726890 * 2 ^ 59
def prefixEnd_4726890 : Nat := 4983230072969 + 3 ^ 40 * 4726890 * 2
def baseEnd_4726890 : Nat := 2427166570931116254836435

theorem tailTrace_4726890 : CollatzResearch.WordTrace tailWord_4726890 prefixEnd_4726890 2427166570931116254836435 := by
  unfold tailWord_4726890
  simp only [CollatzResearch.WordTrace]
  refine ⟨43100960461323073346396531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114935894563528195590390749 43100960461323073346396531)
  ·
    refine ⟨64651440691984610019594797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43100960461323073346396531 64651440691984610019594797)
    ·
      refine ⟨24244290259494228757348049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64651440691984610019594797 24244290259494228757348049)
      ·
        refine ⟨18183217694620671568011037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24244290259494228757348049 18183217694620671568011037)
        ·
          refine ⟨6818706635482751838004139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18183217694620671568011037 6818706635482751838004139)
          ·
            refine ⟨10228059953224127757006209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6818706635482751838004139 10228059953224127757006209)
            ·
              refine ⟨7671044964918095817754657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10228059953224127757006209 7671044964918095817754657)
              ·
                refine ⟨5753283723688571863315993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7671044964918095817754657 5753283723688571863315993)
                ·
                  refine ⟨4314962792766428897486995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5753283723688571863315993 4314962792766428897486995)
                  ·
                    refine ⟨6472444189149643346230493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4314962792766428897486995 6472444189149643346230493)
                    ·
                      refine ⟨2427166570931116254836435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6472444189149643346230493 2427166570931116254836435)
                      ·
                        rfl

theorem cell23_4726890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_4726890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726890 prefixEnd_4726890 := by exact prefixLift 4726890
  have htrace : WordTrace (prefixWord ++ tailWord_4726890) baseStart_4726890 baseEnd_4726890 := by
    simpa [prefixWord, tailWord_4726890, baseEnd_4726890] using wordTrace_append hprefix tailTrace_4726890
  have hstable : (prefixWord ++ tailWord_4726890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726890).length < 2 ^ (prefixWord ++ tailWord_4726890).sum := by decide
  have hdescent : baseEnd_4726890 < baseStart_4726890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726909 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_4726909 : Nat := 118140960795 + 4726909 * 2 ^ 59
def prefixEnd_4726909 : Nat := 4983230072969 + 3 ^ 40 * 4726909 * 2
def baseEnd_4726909 : Nat := 2427176327063551680498847

theorem tailTrace_4726909 : CollatzResearch.WordTrace tailWord_4726909 prefixEnd_4726909 2427176327063551680498847 := by
  unfold tailWord_4726909
  simp only [CollatzResearch.WordTrace]
  refine ⟨172404534832223459630527781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114936356554815639753685187 172404534832223459630527781)
  ·
    refine ⟨32325850281041898680723959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172404534832223459630527781 32325850281041898680723959)
    ·
      refine ⟨48488775421562848021085939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32325850281041898680723959 48488775421562848021085939)
      ·
        refine ⟨72733163132344272031628909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48488775421562848021085939 72733163132344272031628909)
        ·
          refine ⟨27274936174629102011860841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72733163132344272031628909 27274936174629102011860841)
          ·
            refine ⟨20456202130971826508895631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27274936174629102011860841 20456202130971826508895631)
            ·
              refine ⟨30684303196457739763343447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20456202130971826508895631 30684303196457739763343447)
              ·
                refine ⟨46026454794686609645015171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30684303196457739763343447 46026454794686609645015171)
                ·
                  refine ⟨69039682192029914467522757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46026454794686609645015171 69039682192029914467522757)
                  ·
                    refine ⟨12944940411005608962660517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69039682192029914467522757 12944940411005608962660517)
                    ·
                      refine ⟨2427176327063551680498847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12944940411005608962660517 2427176327063551680498847)
                      ·
                        rfl

theorem cell23_4726909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_4726909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726909 prefixEnd_4726909 := by exact prefixLift 4726909
  have htrace : WordTrace (prefixWord ++ tailWord_4726909) baseStart_4726909 baseEnd_4726909 := by
    simpa [prefixWord, tailWord_4726909, baseEnd_4726909] using wordTrace_append hprefix tailTrace_4726909
  have hstable : (prefixWord ++ tailWord_4726909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726909).length < 2 ^ (prefixWord ++ tailWord_4726909).sum := by decide
  have hdescent : baseEnd_4726909 < baseStart_4726909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726949 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_4726949 : Nat := 118140960795 + 4726949 * 2 ^ 59
def prefixEnd_4726949 : Nat := 4983230072969 + 3 ^ 40 * 4726949 * 2
def baseEnd_4726949 : Nat := 809065622096577174666221

theorem tailTrace_4726949 : CollatzResearch.WordTrace tailWord_4726949 prefixEnd_4726949 809065622096577174666221 := by
  unfold tailWord_4726949
  simp only [CollatzResearch.WordTrace]
  refine ⟨172405993752078546461983901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114937329168052364307989267 172405993752078546461983901)
  ·
    refine ⟨64652247657029454923243963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172405993752078546461983901 64652247657029454923243963)
    ·
      refine ⟨96978371485544182384865945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64652247657029454923243963 96978371485544182384865945)
      ·
        refine ⟨72733778614158136788649459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96978371485544182384865945 72733778614158136788649459)
        ·
          refine ⟨109100667921237205182974189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72733778614158136788649459 109100667921237205182974189)
          ·
            refine ⟨40912750470463951943615321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109100667921237205182974189 40912750470463951943615321)
            ·
              refine ⟨30684562852847963957711491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40912750470463951943615321 30684562852847963957711491)
              ·
                refine ⟨46026844279271945936567237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30684562852847963957711491 46026844279271945936567237)
                ·
                  refine ⟨8630033302363489863106357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46026844279271945936567237 8630033302363489863106357)
                  ·
                    refine ⟨809065622096577174666221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8630033302363489863106357 809065622096577174666221)
                    ·
                      rfl

theorem cell23_4726949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_4726949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726949 prefixEnd_4726949 := by exact prefixLift 4726949
  have htrace : WordTrace (prefixWord ++ tailWord_4726949) baseStart_4726949 baseEnd_4726949 := by
    simpa [prefixWord, tailWord_4726949, baseEnd_4726949] using wordTrace_append hprefix tailTrace_4726949
  have hstable : (prefixWord ++ tailWord_4726949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726949).length < 2 ^ (prefixWord ++ tailWord_4726949).sum := by decide
  have hdescent : baseEnd_4726949 < baseStart_4726949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726969 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_4726969 : Nat := 118140960795 + 4726969 * 2 ^ 59
def prefixEnd_4726969 : Nat := 4983230072969 + 3 ^ 40 * 4726969 * 2
def baseEnd_4726969 : Nat := 2427207135902821445748571

theorem tailTrace_4726969 : CollatzResearch.WordTrace tailWord_4726969 prefixEnd_4726969 2427207135902821445748571 := by
  unfold tailWord_4726969
  simp only [CollatzResearch.WordTrace]
  refine ⟨172406723212006089877711961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114937815474670726585141307 172406723212006089877711961)
  ·
    refine ⟨129305042409004567408283971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172406723212006089877711961 129305042409004567408283971)
    ·
      refine ⟨193957563613506851112425957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129305042409004567408283971 193957563613506851112425957)
      ·
        refine ⟨36367043177532534583579867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193957563613506851112425957 36367043177532534583579867)
        ·
          refine ⟨54550564766298801875369801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36367043177532534583579867 54550564766298801875369801)
          ·
            refine ⟨40912923574724101406527351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54550564766298801875369801 40912923574724101406527351)
            ·
              refine ⟨61369385362086152109791027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40912923574724101406527351 61369385362086152109791027)
              ·
                refine ⟨92054078043129228164686541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61369385362086152109791027 92054078043129228164686541)
                ·
                  refine ⟨34520279266173460561757453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92054078043129228164686541 34520279266173460561757453)
                  ·
                    refine ⟨12945104724815047710659045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34520279266173460561757453 12945104724815047710659045)
                    ·
                      refine ⟨2427207135902821445748571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12945104724815047710659045 2427207135902821445748571)
                      ·
                        rfl

theorem cell23_4726969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_4726969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726969 prefixEnd_4726969 := by exact prefixLift 4726969
  have htrace : WordTrace (prefixWord ++ tailWord_4726969) baseStart_4726969 baseEnd_4726969 := by
    simpa [prefixWord, tailWord_4726969, baseEnd_4726969] using wordTrace_append hprefix tailTrace_4726969
  have hstable : (prefixWord ++ tailWord_4726969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726969).length < 2 ^ (prefixWord ++ tailWord_4726969).sum := by decide
  have hdescent : baseEnd_4726969 < baseStart_4726969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4726986 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_4726986 : Nat := 118140960795 + 4726986 * 2 ^ 59
def prefixEnd_4726986 : Nat := 4983230072969 + 3 ^ 40 * 4726986 * 2
def baseEnd_4726986 : Nat := 2427215865073947879235993

theorem tailTrace_4726986 : CollatzResearch.WordTrace tailWord_4726986 prefixEnd_4726986 2427215865073947879235993 := by
  unfold tailWord_4726986
  simp only [CollatzResearch.WordTrace]
  refine ⟨43101835813236125445270203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114938228835296334520720541 43101835813236125445270203)
  ·
    refine ⟨64652753719854188167905305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43101835813236125445270203 64652753719854188167905305)
    ·
      refine ⟨48489565289890641125928979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64652753719854188167905305 48489565289890641125928979)
      ·
        refine ⟨72734347934835961688893469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48489565289890641125928979 72734347934835961688893469)
        ·
          refine ⟨27275380475563485633335051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72734347934835961688893469 27275380475563485633335051)
          ·
            refine ⟨40913070713345228450002577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27275380475563485633335051 40913070713345228450002577)
            ·
              refine ⟨30684803035008921337501933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40913070713345228450002577 30684803035008921337501933)
              ·
                refine ⟨11506801138128345501563225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30684803035008921337501933 11506801138128345501563225)
                ·
                  refine ⟨8630100853596259126172419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11506801138128345501563225 8630100853596259126172419)
                  ·
                    refine ⟨12945151280394388689258629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8630100853596259126172419 12945151280394388689258629)
                    ·
                      refine ⟨2427215865073947879235993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12945151280394388689258629 2427215865073947879235993)
                      ·
                        rfl

theorem cell23_4726986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_4726986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4726986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4726986 prefixEnd_4726986 := by exact prefixLift 4726986
  have htrace : WordTrace (prefixWord ++ tailWord_4726986) baseStart_4726986 baseEnd_4726986 := by
    simpa [prefixWord, tailWord_4726986, baseEnd_4726986] using wordTrace_append hprefix tailTrace_4726986
  have hstable : (prefixWord ++ tailWord_4726986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4726986).length < 2 ^ (prefixWord ++ tailWord_4726986).sum := by decide
  have hdescent : baseEnd_4726986 < baseStart_4726986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4726986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727009 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 8]
def baseStart_4727009 : Nat := 118140960795 + 4727009 * 2 ^ 59
def prefixEnd_4727009 : Nat := 4983230072969 + 3 ^ 40 * 4727009 * 2
def baseEnd_4727009 : Nat := 269691963903222365472043

theorem tailTrace_4727009 : CollatzResearch.WordTrace tailWord_4727009 prefixEnd_4727009 269691963903222365472043 := by
  unfold tailWord_4727009
  simp only [CollatzResearch.WordTrace]
  refine ⟨172408182131861176709168081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114938788087907451139445387 172408182131861176709168081)
  ·
    refine ⟨129306136598895882531876061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172408182131861176709168081 129306136598895882531876061)
    ·
      refine ⟨48489801224585955949453523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129306136598895882531876061 48489801224585955949453523)
      ·
        refine ⟨72734701836878933924180285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48489801224585955949453523 72734701836878933924180285)
        ·
          refine ⟨27275513188829600221567607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72734701836878933924180285 27275513188829600221567607)
          ·
            refine ⟨40913269783244400332351411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27275513188829600221567607 40913269783244400332351411)
            ·
              refine ⟨61369904674866600498527117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40913269783244400332351411 61369904674866600498527117)
              ·
                refine ⟨23013714253074975186947669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61369904674866600498527117 23013714253074975186947669)
                ·
                  refine ⟨269691963903222365472043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23013714253074975186947669 269691963903222365472043)
                  ·
                    rfl

theorem cell23_4727009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 8].length) (baseStart_4727009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727009 prefixEnd_4727009 := by exact prefixLift 4727009
  have htrace : WordTrace (prefixWord ++ tailWord_4727009) baseStart_4727009 baseEnd_4727009 := by
    simpa [prefixWord, tailWord_4727009, baseEnd_4727009] using wordTrace_append hprefix tailTrace_4727009
  have hstable : (prefixWord ++ tailWord_4727009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727009).length < 2 ^ (prefixWord ++ tailWord_4727009).sum := by decide
  have hdescent : baseEnd_4727009 < baseStart_4727009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727013 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_4727013 : Nat := 118140960795 + 4727013 * 2 ^ 59
def prefixEnd_4727013 : Nat := 4983230072969 + 3 ^ 40 * 4727013 * 2
def baseEnd_4727013 : Nat := 809076576350539757866123

theorem tailTrace_4727013 : CollatzResearch.WordTrace tailWord_4727013 prefixEnd_4727013 809076576350539757866123 := by
  unfold tailWord_4727013
  simp only [CollatzResearch.WordTrace]
  refine ⟨172408328023846685392313693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114938885349231123594875795 172408328023846685392313693)
  ·
    refine ⟨64653123008942507022117635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172408328023846685392313693 64653123008942507022117635)
    ·
      refine ⟨96979684513413760533176453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64653123008942507022117635 96979684513413760533176453)
      ·
        refine ⟨18183690846265080099970585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96979684513413760533176453 18183690846265080099970585)
        ·
          refine ⟨13637768134698810074977939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18183690846265080099970585 13637768134698810074977939)
          ·
            refine ⟨20456652202048215112466909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13637768134698810074977939 20456652202048215112466909)
            ·
              refine ⟨7671244575768080667175091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20456652202048215112466909 7671244575768080667175091)
              ·
                refine ⟨11506866863652121000762637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7671244575768080667175091 11506866863652121000762637)
                ·
                  refine ⟨4315075073869545375285989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11506866863652121000762637 4315075073869545375285989)
                  ·
                    refine ⟨809076576350539757866123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315075073869545375285989 809076576350539757866123)
                    ·
                      rfl

theorem cell23_4727013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_4727013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727013 prefixEnd_4727013 := by exact prefixLift 4727013
  have htrace : WordTrace (prefixWord ++ tailWord_4727013) baseStart_4727013 baseEnd_4727013 := by
    simpa [prefixWord, tailWord_4727013, baseEnd_4727013] using wordTrace_append hprefix tailTrace_4727013
  have hstable : (prefixWord ++ tailWord_4727013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727013).length < 2 ^ (prefixWord ++ tailWord_4727013).sum := by decide
  have hdescent : baseEnd_4727013 < baseStart_4727013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727093 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_4727093 : Nat := 118140960795 + 4727093 * 2 ^ 59
def prefixEnd_4727093 : Nat := 4983230072969 + 3 ^ 40 * 4727093 * 2
def baseEnd_4727093 : Nat := 2427270807503978960598001

theorem tailTrace_4727093 : CollatzResearch.WordTrace tailWord_4727093 prefixEnd_4727093 2427270807503978960598001 := by
  unfold tailWord_4727093
  simp only [CollatzResearch.WordTrace]
  refine ⟨172411245863556859055225933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114940830575704572703483955 172411245863556859055225933)
  ·
    refine ⟨64654217198833822145709725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172411245863556859055225933 64654217198833822145709725)
    ·
      refine ⟨24245331449562683304641147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64654217198833822145709725 24245331449562683304641147)
      ·
        refine ⟨36367997174344024956961721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24245331449562683304641147 36367997174344024956961721)
        ·
          refine ⟨27275997880758018717721291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36367997174344024956961721 27275997880758018717721291)
          ·
            refine ⟨40913996821137028076581937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27275997880758018717721291 40913996821137028076581937)
            ·
              refine ⟨30685497615852771057436453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40913996821137028076581937 30685497615852771057436453)
              ·
                refine ⟨5753530802972394573269335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30685497615852771057436453 5753530802972394573269335)
                ·
                  refine ⟨8630296204458591859904003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5753530802972394573269335 8630296204458591859904003)
                  ·
                    refine ⟨12945444306687887789856005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8630296204458591859904003 12945444306687887789856005)
                    ·
                      refine ⟨2427270807503978960598001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12945444306687887789856005 2427270807503978960598001)
                      ·
                        rfl

theorem cell23_4727093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_4727093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727093 prefixEnd_4727093 := by exact prefixLift 4727093
  have htrace : WordTrace (prefixWord ++ tailWord_4727093) baseStart_4727093 baseEnd_4727093 := by
    simpa [prefixWord, tailWord_4727093, baseEnd_4727093] using wordTrace_append hprefix tailTrace_4727093
  have hstable : (prefixWord ++ tailWord_4727093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727093).length < 2 ^ (prefixWord ++ tailWord_4727093).sum := by decide
  have hdescent : baseEnd_4727093 < baseStart_4727093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727097 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4727097 : Nat := 118140960795 + 4727097 * 2 ^ 59
def prefixEnd_4727097 : Nat := 4983230072969 + 3 ^ 40 * 4727097 * 2
def baseEnd_4727097 : Nat := 2427272861426596944947983

theorem tailTrace_4727097 : CollatzResearch.WordTrace tailWord_4727097 prefixEnd_4727097 2427272861426596944947983 := by
  unfold tailWord_4727097
  simp only [CollatzResearch.WordTrace]
  refine ⟨172411391755542367738371545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114940927837028245158914363 172411391755542367738371545)
  ·
    refine ⟨129308543816656775803778659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172411391755542367738371545 129308543816656775803778659)
    ·
      refine ⟨193962815724985163705667989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129308543816656775803778659 193962815724985163705667989)
      ·
        refine ⟨9092006987108679548703187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 193962815724985163705667989 9092006987108679548703187)
        ·
          refine ⟨13638010480663019323054781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9092006987108679548703187 13638010480663019323054781)
          ·
            refine ⟨5114253930248632246145543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13638010480663019323054781 5114253930248632246145543)
            ·
              refine ⟨7671380895372948369218315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114253930248632246145543 7671380895372948369218315)
              ·
                refine ⟨11507071343059422553827473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7671380895372948369218315 11507071343059422553827473)
                ·
                  refine ⟨8630303507294566915370605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11507071343059422553827473 8630303507294566915370605)
                  ·
                    refine ⟨3236363815235462593263977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8630303507294566915370605 3236363815235462593263977)
                    ·
                      refine ⟨2427272861426596944947983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3236363815235462593263977 2427272861426596944947983)
                      ·
                        rfl

theorem cell23_4727097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4727097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727097 prefixEnd_4727097 := by exact prefixLift 4727097
  have htrace : WordTrace (prefixWord ++ tailWord_4727097) baseStart_4727097 baseEnd_4727097 := by
    simpa [prefixWord, tailWord_4727097, baseEnd_4727097] using wordTrace_append hprefix tailTrace_4727097
  have hstable : (prefixWord ++ tailWord_4727097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727097).length < 2 ^ (prefixWord ++ tailWord_4727097).sum := by decide
  have hdescent : baseEnd_4727097 < baseStart_4727097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727120 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 2, 4]
def baseStart_4727120 : Nat := 118140960795 + 4727120 * 2 ^ 59
def prefixEnd_4727120 : Nat := 4983230072969 + 3 ^ 40 * 4727120 * 2
def baseEnd_4727120 : Nat := 809094890493883451653459

theorem tailTrace_4727120 : CollatzResearch.WordTrace tailWord_4727120 prefixEnd_4727120 809094890493883451653459 := by
  unfold tailWord_4727120
  simp only [CollatzResearch.WordTrace]
  refine ⟨86206115317229521333229407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114941487089639361777639209 86206115317229521333229407)
  ·
    refine ⟨129309172975844281999844111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86206115317229521333229407 129309172975844281999844111)
    ·
      refine ⟨193963759463766422999766167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129309172975844281999844111 193963759463766422999766167)
      ·
        refine ⟨290945639195649634499649251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193963759463766422999766167 290945639195649634499649251)
        ·
          refine ⟨436418458793474451749473877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290945639195649634499649251 436418458793474451749473877)
          ·
            refine ⟨5114278813986028731439147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 436418458793474451749473877 5114278813986028731439147)
            ·
              refine ⟨7671418220979043097158721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114278813986028731439147 7671418220979043097158721)
              ·
                refine ⟨5753563665734282322869041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7671418220979043097158721 5753563665734282322869041)
                ·
                  refine ⟨4315172749300711742151781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5753563665734282322869041 4315172749300711742151781)
                  ·
                    refine ⟨809094890493883451653459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315172749300711742151781 809094890493883451653459)
                    ·
                      rfl

theorem cell23_4727120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2, 4].length) (baseStart_4727120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727120 prefixEnd_4727120 := by exact prefixLift 4727120
  have htrace : WordTrace (prefixWord ++ tailWord_4727120) baseStart_4727120 baseEnd_4727120 := by
    simpa [prefixWord, tailWord_4727120, baseEnd_4727120] using wordTrace_append hprefix tailTrace_4727120
  have hstable : (prefixWord ++ tailWord_4727120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727120).length < 2 ^ (prefixWord ++ tailWord_4727120).sum := by decide
  have hdescent : baseEnd_4727120 < baseStart_4727120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727127 : List Nat := [1, 1, 3, 2, 3, 1, 1, 6, 1, 2, 2]
def baseStart_4727127 : Nat := 118140960795 + 4727127 * 2 ^ 59
def prefixEnd_4727127 : Nat := 4983230072969 + 3 ^ 40 * 4727127 * 2
def baseEnd_4727127 : Nat := 2427288265846231827572845

theorem tailTrace_4727127 : CollatzResearch.WordTrace tailWord_4727127 prefixEnd_4727127 2427288265846231827572845 := by
  unfold tailWord_4727127
  simp only [CollatzResearch.WordTrace]
  refine ⟨172412485945433682861963635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114941657296955788574642423 172412485945433682861963635)
  ·
    refine ⟨258618728918150524292945453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172412485945433682861963635 258618728918150524292945453)
    ·
      refine ⟨96982023344306446609854545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258618728918150524292945453 96982023344306446609854545)
      ·
        refine ⟨72736517508229834957390909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96982023344306446609854545 72736517508229834957390909)
        ·
          refine ⟨27276194065586188109021591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72736517508229834957390909 27276194065586188109021591)
          ·
            refine ⟨40914291098379282163532387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27276194065586188109021591 40914291098379282163532387)
            ·
              refine ⟨61371436647568923245298581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40914291098379282163532387 61371436647568923245298581)
              ·
                refine ⟨2876786092854793277123371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61371436647568923245298581 2876786092854793277123371)
                ·
                  refine ⟨4315179139282189915685057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876786092854793277123371 4315179139282189915685057)
                  ·
                    refine ⟨3236384354461642436763793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4315179139282189915685057 3236384354461642436763793)
                    ·
                      refine ⟨2427288265846231827572845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3236384354461642436763793 2427288265846231827572845)
                      ·
                        rfl

theorem cell23_4727127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_4727127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727127 prefixEnd_4727127 := by exact prefixLift 4727127
  have htrace : WordTrace (prefixWord ++ tailWord_4727127) baseStart_4727127 baseEnd_4727127 := by
    simpa [prefixWord, tailWord_4727127, baseEnd_4727127] using wordTrace_append hprefix tailTrace_4727127
  have hstable : (prefixWord ++ tailWord_4727127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727127).length < 2 ^ (prefixWord ++ tailWord_4727127).sum := by decide
  have hdescent : baseEnd_4727127 < baseStart_4727127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727178 : List Nat := [3, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2]
def baseStart_4727178 : Nat := 118140960795 + 4727178 * 2 ^ 59
def prefixEnd_4727178 : Nat := 4983230072969 + 3 ^ 40 * 4727178 * 2
def baseEnd_4727178 : Nat := 2427314453359611128035111

theorem tailTrace_4727178 : CollatzResearch.WordTrace tailWord_4727178 prefixEnd_4727178 2427314453359611128035111 := by
  unfold tailWord_4727178
  simp only [CollatzResearch.WordTrace]
  refine ⟨43103586517062229643017547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114942897378832612381380125 43103586517062229643017547)
  ·
    refine ⟨64655379775593344464526321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43103586517062229643017547 64655379775593344464526321)
    ·
      refine ⟨48491534831695008348394741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64655379775593344464526321 48491534831695008348394741)
      ·
        refine ⟨4546081390471407032662007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48491534831695008348394741 4546081390471407032662007)
        ·
          refine ⟨6819122085707110548993011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4546081390471407032662007 6819122085707110548993011)
          ·
            refine ⟨10228683128560665823489517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6819122085707110548993011 10228683128560665823489517)
            ·
              refine ⟨3835756173210249683808569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10228683128560665823489517 3835756173210249683808569)
              ·
                refine ⟨2876817129907687262856427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3835756173210249683808569 2876817129907687262856427)
                ·
                  refine ⟨4315225694861530894284641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876817129907687262856427 4315225694861530894284641)
                  ·
                    refine ⟨3236419271146148170713481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4315225694861530894284641 3236419271146148170713481)
                    ·
                      refine ⟨2427314453359611128035111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3236419271146148170713481 2427314453359611128035111)
                      ·
                        rfl

theorem cell23_4727178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_4727178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727178 prefixEnd_4727178 := by exact prefixLift 4727178
  have htrace : WordTrace (prefixWord ++ tailWord_4727178) baseStart_4727178 baseEnd_4727178 := by
    simpa [prefixWord, tailWord_4727178, baseEnd_4727178] using wordTrace_append hprefix tailTrace_4727178
  have hstable : (prefixWord ++ tailWord_4727178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727178).length < 2 ^ (prefixWord ++ tailWord_4727178).sum := by decide
  have hdescent : baseEnd_4727178 < baseStart_4727178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727194 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3]
def baseStart_4727194 : Nat := 118140960795 + 4727194 * 2 ^ 59
def prefixEnd_4727194 : Nat := 4983230072969 + 3 ^ 40 * 4727194 * 2
def baseEnd_4727194 : Nat := 2427322669050083065435037

theorem tailTrace_4727194 : CollatzResearch.WordTrace tailWord_4727194 prefixEnd_4727194 2427322669050083065435037 := by
  unfold tailWord_4727194
  simp only [CollatzResearch.WordTrace]
  refine ⟨43103732409047738326163159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114943286424127302203101757 43103732409047738326163159)
  ·
    refine ⟨64655598613571607489244739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43103732409047738326163159 64655598613571607489244739)
    ·
      refine ⟨96983397920357411233867109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64655598613571607489244739 96983397920357411233867109)
      ·
        refine ⟨18184387110067014606350083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96983397920357411233867109 18184387110067014606350083)
        ·
          refine ⟨27276580665100521909525125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18184387110067014606350083 27276580665100521909525125)
          ·
            refine ⟨5114358874706347858035961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27276580665100521909525125 5114358874706347858035961)
            ·
              refine ⟨3835769156029760893526971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5114358874706347858035961 3835769156029760893526971)
              ·
                refine ⟨5753653734044641340290457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3835769156029760893526971 5753653734044641340290457)
                ·
                  refine ⟨4315240300533481005217843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5753653734044641340290457 4315240300533481005217843)
                  ·
                    refine ⟨6472860450800221507826765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4315240300533481005217843 6472860450800221507826765)
                    ·
                      refine ⟨2427322669050083065435037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6472860450800221507826765 2427322669050083065435037)
                      ·
                        rfl

theorem cell23_4727194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_4727194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727194 prefixEnd_4727194 := by exact prefixLift 4727194
  have htrace : WordTrace (prefixWord ++ tailWord_4727194) baseStart_4727194 baseEnd_4727194 := by
    simpa [prefixWord, tailWord_4727194, baseEnd_4727194] using wordTrace_append hprefix tailTrace_4727194
  have hstable : (prefixWord ++ tailWord_4727194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727194).length < 2 ^ (prefixWord ++ tailWord_4727194).sum := by decide
  have hdescent : baseEnd_4727194 < baseStart_4727194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727240 : List Nat := [2, 1, 3, 1, 3, 3, 1, 4, 5]
def baseStart_4727240 : Nat := 118140960795 + 4727240 * 2 ^ 59
def prefixEnd_4727240 : Nat := 4983230072969 + 3 ^ 40 * 4727240 * 2
def baseEnd_4727240 : Nat := 269705143240021098384425

theorem tailTrace_4727240 : CollatzResearch.WordTrace tailWord_4727240 prefixEnd_4727240 269705143240021098384425 := by
  unfold tailWord_4727240
  simp only [CollatzResearch.WordTrace]
  refine ⟨86208303697012151580413587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114944404929349535440551449 86208303697012151580413587)
  ·
    refine ⟨129312455545518227370620381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86208303697012151580413587 129312455545518227370620381)
    ·
      refine ⟨48492170829569335263982643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129312455545518227370620381 48492170829569335263982643)
      ·
        refine ⟨72738256244354002895973965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48492170829569335263982643 72738256244354002895973965)
        ·
          refine ⟨27276846091632751085990237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72738256244354002895973965 27276846091632751085990237)
          ·
            refine ⟨10228817284362281657246339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27276846091632751085990237 10228817284362281657246339)
            ·
              refine ⟨15343225926543422485869509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10228817284362281657246339 15343225926543422485869509)
              ·
                refine ⟨2876854861226891716100533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15343225926543422485869509 2876854861226891716100533)
                ·
                  refine ⟨269705143240021098384425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2876854861226891716100533 269705143240021098384425)
                  ·
                    rfl

theorem cell23_4727240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 5].length) (baseStart_4727240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727240 prefixEnd_4727240 := by exact prefixLift 4727240
  have htrace : WordTrace (prefixWord ++ tailWord_4727240) baseStart_4727240 baseEnd_4727240 := by
    simpa [prefixWord, tailWord_4727240, baseEnd_4727240] using wordTrace_append hprefix tailTrace_4727240
  have hstable : (prefixWord ++ tailWord_4727240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727240).length < 2 ^ (prefixWord ++ tailWord_4727240).sum := by decide
  have hdescent : baseEnd_4727240 < baseStart_4727240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727273 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_4727273 : Nat := 118140960795 + 4727273 * 2 ^ 59
def prefixEnd_4727273 : Nat := 4983230072969 + 3 ^ 40 * 4727273 * 2
def baseEnd_4727273 : Nat := 2427363234021788256347173

theorem tailTrace_4727273 : CollatzResearch.WordTrace tailWord_4727273 prefixEnd_4727273 2427363234021788256347173 := by
  unfold tailWord_4727273
  simp only [CollatzResearch.WordTrace]
  refine ⟨172417811002904749796778473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114945207335269833197852315 172417811002904749796778473)
  ·
    refine ⟨129313358252178562347583855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172417811002904749796778473 129313358252178562347583855)
    ·
      refine ⟨193970037378267843521375783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129313358252178562347583855 193970037378267843521375783)
      ·
        refine ⟨290955056067401765282063675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193970037378267843521375783 290955056067401765282063675)
        ·
          refine ⟨436432584101102647923095513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290955056067401765282063675 436432584101102647923095513)
          ·
            refine ⟨327324438075826985942321635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436432584101102647923095513 327324438075826985942321635)
            ·
              refine ⟨490986657113740478913482453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327324438075826985942321635 490986657113740478913482453)
              ·
                refine ⟨11507499776103292474534745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 490986657113740478913482453 11507499776103292474534745)
                ·
                  refine ⟨8630624832077469355901059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11507499776103292474534745 8630624832077469355901059)
                  ·
                    refine ⟨12945937248116204033851589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8630624832077469355901059 12945937248116204033851589)
                    ·
                      refine ⟨2427363234021788256347173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12945937248116204033851589 2427363234021788256347173)
                      ·
                        rfl

theorem cell23_4727273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_4727273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727273 prefixEnd_4727273 := by exact prefixLift 4727273
  have htrace : WordTrace (prefixWord ++ tailWord_4727273) baseStart_4727273 baseEnd_4727273 := by
    simpa [prefixWord, tailWord_4727273, baseEnd_4727273] using wordTrace_append hprefix tailTrace_4727273
  have hstable : (prefixWord ++ tailWord_4727273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727273).length < 2 ^ (prefixWord ++ tailWord_4727273).sum := by decide
  have hdescent : baseEnd_4727273 < baseStart_4727273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727283 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 5, 4]
def baseStart_4727283 : Nat := 118140960795 + 4727283 * 2 ^ 59
def prefixEnd_4727283 : Nat := 4983230072969 + 3 ^ 40 * 4727283 * 2
def baseEnd_4727283 : Nat := 809122789609444405740709

theorem tailTrace_4727283 : CollatzResearch.WordTrace tailWord_4727283 prefixEnd_4727283 809122789609444405740709 := by
  unfold tailWord_4727283
  simp only [CollatzResearch.WordTrace]
  refine ⟨172418175732868521504642503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114945450488579014336428335 172418175732868521504642503)
  ·
    refine ⟨258627263599302782256963755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172418175732868521504642503 258627263599302782256963755)
    ·
      refine ⟨387940895398954173385445633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258627263599302782256963755 387940895398954173385445633)
      ·
        refine ⟨290955671549215630039084225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387940895398954173385445633 290955671549215630039084225)
        ·
          refine ⟨218216753661911722529313169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290955671549215630039084225 218216753661911722529313169)
          ·
            refine ⟨163662565246433791896984877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218216753661911722529313169 163662565246433791896984877)
            ·
              refine ⟨61373461967412671961369329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163662565246433791896984877 61373461967412671961369329)
              ·
                refine ⟨46030096475559503971026997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61373461967412671961369329 46030096475559503971026997)
                ·
                  refine ⟨4315321544583703497283781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46030096475559503971026997 4315321544583703497283781)
                  ·
                    refine ⟨809122789609444405740709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315321544583703497283781 809122789609444405740709)
                    ·
                      rfl

theorem cell23_4727283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 4].length) (baseStart_4727283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727283 prefixEnd_4727283 := by exact prefixLift 4727283
  have htrace : WordTrace (prefixWord ++ tailWord_4727283) baseStart_4727283 baseEnd_4727283 := by
    simpa [prefixWord, tailWord_4727283, baseEnd_4727283] using wordTrace_append hprefix tailTrace_4727283
  have hstable : (prefixWord ++ tailWord_4727283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727283).length < 2 ^ (prefixWord ++ tailWord_4727283).sum := by decide
  have hdescent : baseEnd_4727283 < baseStart_4727283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727310 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_4727310 : Nat := 118140960795 + 4727310 * 2 ^ 59
def prefixEnd_4727310 : Nat := 4983230072969 + 3 ^ 40 * 4727310 * 2
def baseEnd_4727310 : Nat := 2427382232806004611584503

theorem tailTrace_4727310 : CollatzResearch.WordTrace tailWord_4727310 prefixEnd_4727310 2427382232806004611584503 := by
  unfold tailWord_4727310
  simp only [CollatzResearch.WordTrace]
  refine ⟨21552395062971338139484423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114946107002513803410583589 21552395062971338139484423)
  ·
    refine ⟨32328592594457007209226635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21552395062971338139484423 32328592594457007209226635)
    ·
      refine ⟨48492888891685510813839953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32328592594457007209226635 48492888891685510813839953)
      ·
        refine ⟨36369666668764133110379965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48492888891685510813839953 36369666668764133110379965)
        ·
          refine ⟨13638625000786549916392487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36369666668764133110379965 13638625000786549916392487)
          ·
            refine ⟨20457937501179824874588731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13638625000786549916392487 20457937501179824874588731)
            ·
              refine ⟨30686906251769737311883097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20457937501179824874588731 30686906251769737311883097)
              ·
                refine ⟨23015179688827302983912323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30686906251769737311883097 23015179688827302983912323)
                ·
                  refine ⟨34522769533240954475868485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23015179688827302983912323 34522769533240954475868485)
                  ·
                    refine ⟨6473019287482678964225341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34522769533240954475868485 6473019287482678964225341)
                    ·
                      refine ⟨2427382232806004611584503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6473019287482678964225341 2427382232806004611584503)
                      ·
                        rfl

theorem cell23_4727310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_4727310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727310 prefixEnd_4727310 := by exact prefixLift 4727310
  have htrace : WordTrace (prefixWord ++ tailWord_4727310) baseStart_4727310 baseEnd_4727310 := by
    simpa [prefixWord, tailWord_4727310, baseEnd_4727310] using wordTrace_append hprefix tailTrace_4727310
  have hstable : (prefixWord ++ tailWord_4727310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727310).length < 2 ^ (prefixWord ++ tailWord_4727310).sum := by decide
  have hdescent : baseEnd_4727310 < baseStart_4727310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727340 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 3]
def baseStart_4727340 : Nat := 118140960795 + 4727340 * 2 ^ 59
def prefixEnd_4727340 : Nat := 4983230072969 + 3 ^ 40 * 4727340 * 2
def baseEnd_4727340 : Nat := 2427397637225639494209365

theorem tailTrace_4727340 : CollatzResearch.WordTrace tailWord_4727340 prefixEnd_4727340 2427397637225639494209365 := by
  unfold tailWord_4727340
  simp only [CollatzResearch.WordTrace]
  refine ⟨86210127346831010119733737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114946836462441346826311649 86210127346831010119733737)
  ·
    refine ⟨64657595510123257589800303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86210127346831010119733737 64657595510123257589800303)
    ·
      refine ⟨96986393265184886384700455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64657595510123257589800303 96986393265184886384700455)
      ·
        refine ⟨145479589897777329577050683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96986393265184886384700455 145479589897777329577050683)
        ·
          refine ⟨218219384846665994365576025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145479589897777329577050683 218219384846665994365576025)
          ·
            refine ⟨163664538634999495774182019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218219384846665994365576025 163664538634999495774182019)
            ·
              refine ⟨245496807952499243661273029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163664538634999495774182019 245496807952499243661273029)
              ·
                refine ⟨46030651491093608186488693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245496807952499243661273029 46030651491093608186488693)
                ·
                  refine ⟨4315373577290025767483315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46030651491093608186488693 4315373577290025767483315)
                  ·
                    refine ⟨6473060365935038651224973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4315373577290025767483315 6473060365935038651224973)
                    ·
                      refine ⟨2427397637225639494209365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6473060365935038651224973 2427397637225639494209365)
                      ·
                        rfl

theorem cell23_4727340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_4727340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727340 prefixEnd_4727340 := by exact prefixLift 4727340
  have htrace : WordTrace (prefixWord ++ tailWord_4727340) baseStart_4727340 baseEnd_4727340 := by
    simpa [prefixWord, tailWord_4727340, baseEnd_4727340] using wordTrace_append hprefix tailTrace_4727340
  have hstable : (prefixWord ++ tailWord_4727340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727340).length < 2 ^ (prefixWord ++ tailWord_4727340).sum := by decide
  have hdescent : baseEnd_4727340 < baseStart_4727340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727341 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4727341 : Nat := 118140960795 + 4727341 * 2 ^ 59
def prefixEnd_4727341 : Nat := 4983230072969 + 3 ^ 40 * 4727341 * 2
def baseEnd_4727341 : Nat := 2427398150706293990296861

theorem tailTrace_4727341 : CollatzResearch.WordTrace tailWord_4727341 prefixEnd_4727341 2427398150706293990296861 := by
  unfold tailWord_4727341
  simp only [CollatzResearch.WordTrace]
  refine ⟨172420291166658397410253877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114946860777772264940169251 172420291166658397410253877)
  ·
    refine ⟨16164402296874224757211301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172420291166658397410253877 16164402296874224757211301)
    ·
      refine ⟨3030825430663917141977119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16164402296874224757211301 3030825430663917141977119)
      ·
        refine ⟨4546238145995875712965679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3030825430663917141977119 4546238145995875712965679)
        ·
          refine ⟨6819357218993813569448519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4546238145995875712965679 6819357218993813569448519)
          ·
            refine ⟨10229035828490720354172779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6819357218993813569448519 10229035828490720354172779)
            ·
              refine ⟨15343553742736080531259169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10229035828490720354172779 15343553742736080531259169)
              ·
                refine ⟨11507665307052060398444377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15343553742736080531259169 11507665307052060398444377)
                ·
                  refine ⟨8630748980289045298833283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11507665307052060398444377 8630748980289045298833283)
                  ·
                    refine ⟨12946123470433567948249925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8630748980289045298833283 12946123470433567948249925)
                    ·
                      refine ⟨2427398150706293990296861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12946123470433567948249925 2427398150706293990296861)
                      ·
                        rfl

theorem cell23_4727341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4727341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727341 prefixEnd_4727341 := by exact prefixLift 4727341
  have htrace : WordTrace (prefixWord ++ tailWord_4727341) baseStart_4727341 baseEnd_4727341 := by
    simpa [prefixWord, tailWord_4727341, baseEnd_4727341] using wordTrace_append hprefix tailTrace_4727341
  have hstable : (prefixWord ++ tailWord_4727341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727341).length < 2 ^ (prefixWord ++ tailWord_4727341).sum := by decide
  have hdescent : baseEnd_4727341 < baseStart_4727341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727377 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 1, 5]
def baseStart_4727377 : Nat := 118140960795 + 4727377 * 2 ^ 59
def prefixEnd_4727377 : Nat := 4983230072969 + 3 ^ 40 * 4727377 * 2
def baseEnd_4727377 : Nat := 809138878669951949815565

theorem tailTrace_4727377 : CollatzResearch.WordTrace tailWord_4727377 prefixEnd_4727377 809138878669951949815565 := by
  unfold tailWord_4727377
  simp only [CollatzResearch.WordTrace]
  refine ⟨172421604194527975558564385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114947736129685317039042923 172421604194527975558564385)
  ·
    refine ⟨129316203145895981668923289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172421604194527975558564385 129316203145895981668923289)
    ·
      refine ⟨96987152359421986251692467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129316203145895981668923289 96987152359421986251692467)
      ·
        refine ⟨145480728539132979377538701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96987152359421986251692467 145480728539132979377538701)
        ·
          refine ⟨54555273202174867266577013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145480728539132979377538701 54555273202174867266577013)
          ·
            refine ⟨5114556862703893806241595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54555273202174867266577013 5114556862703893806241595)
            ·
              refine ⟨7671835294055840709362393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114556862703893806241595 7671835294055840709362393)
              ·
                refine ⟨5753876470541880532021795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7671835294055840709362393 5753876470541880532021795)
                ·
                  refine ⟨8630814705812820798032693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5753876470541880532021795 8630814705812820798032693)
                  ·
                    refine ⟨809138878669951949815565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8630814705812820798032693 809138878669951949815565)
                    ·
                      rfl

theorem cell23_4727377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_4727377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727377 prefixEnd_4727377 := by exact prefixLift 4727377
  have htrace : WordTrace (prefixWord ++ tailWord_4727377) baseStart_4727377 baseEnd_4727377 := by
    simpa [prefixWord, tailWord_4727377, baseEnd_4727377] using wordTrace_append hprefix tailTrace_4727377
  have hstable : (prefixWord ++ tailWord_4727377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727377).length < 2 ^ (prefixWord ++ tailWord_4727377).sum := by decide
  have hdescent : baseEnd_4727377 < baseStart_4727377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727408 : List Nat := [2, 1, 1, 1, 7, 2, 2, 2, 1, 1, 3]
def baseStart_4727408 : Nat := 118140960795 + 4727408 * 2 ^ 59
def prefixEnd_4727408 : Nat := 4983230072969 + 3 ^ 40 * 4727408 * 2
def baseEnd_4727408 : Nat := 2427432553910145228159053

theorem tailTrace_4727408 : CollatzResearch.WordTrace tailWord_4727408 prefixEnd_4727408 2427432553910145228159053 := by
  unfold tailWord_4727408
  simp only [CollatzResearch.WordTrace]
  refine ⟨86211367428707833926471439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114948489904943778568628585 86211367428707833926471439)
  ·
    refine ⟨129317051143061750889707159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86211367428707833926471439 129317051143061750889707159)
    ·
      refine ⟨193975576714592626334560739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129317051143061750889707159 193975576714592626334560739)
      ·
        refine ⟨290963365071888939501841109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193975576714592626334560739 290963365071888939501841109)
        ·
          refine ⟨6819453868872397019574401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 290963365071888939501841109 6819453868872397019574401)
          ·
            refine ⟨5114590401654297764680801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6819453868872397019574401 5114590401654297764680801)
            ·
              refine ⟨3835942801240723323510601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5114590401654297764680801 3835942801240723323510601)
              ·
                refine ⟨2876957100930542492632951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3835942801240723323510601 2876957100930542492632951)
                ·
                  refine ⟨4315435651395813738949427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876957100930542492632951 4315435651395813738949427)
                  ·
                    refine ⟨6473153477093720608424141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4315435651395813738949427 6473153477093720608424141)
                    ·
                      refine ⟨2427432553910145228159053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6473153477093720608424141 2427432553910145228159053)
                      ·
                        rfl

theorem cell23_4727408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 1, 3].length) (baseStart_4727408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727408 prefixEnd_4727408 := by exact prefixLift 4727408
  have htrace : WordTrace (prefixWord ++ tailWord_4727408) baseStart_4727408 baseEnd_4727408 := by
    simpa [prefixWord, tailWord_4727408, baseEnd_4727408] using wordTrace_append hprefix tailTrace_4727408
  have hstable : (prefixWord ++ tailWord_4727408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727408).length < 2 ^ (prefixWord ++ tailWord_4727408).sum := by decide
  have hdescent : baseEnd_4727408 < baseStart_4727408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727433 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 4, 7]
def baseStart_4727433 : Nat := 118140960795 + 4727433 * 2 ^ 59
def prefixEnd_4727433 : Nat := 4983230072969 + 3 ^ 40 * 4727433 * 2
def baseEnd_4727433 : Nat := 809148463642169210115479

theorem tailTrace_4727433 : CollatzResearch.WordTrace tailWord_4727433 prefixEnd_4727433 809148463642169210115479 := by
  unfold tailWord_4727433
  simp only [CollatzResearch.WordTrace]
  refine ⟨172423646682325097122602953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114949097788216731415068635 172423646682325097122602953)
  ·
    refine ⟨129317735011743822841952215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172423646682325097122602953 129317735011743822841952215)
    ·
      refine ⟨193976602517615734262928323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129317735011743822841952215 193976602517615734262928323)
      ·
        refine ⟨290964903776423601394392485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193976602517615734262928323 290964903776423601394392485)
        ·
          refine ⟨54555919458079425261448591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 290964903776423601394392485 54555919458079425261448591)
          ·
            refine ⟨81833879187119137892172887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54555919458079425261448591 81833879187119137892172887)
            ·
              refine ⟨122750818780678706838259331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81833879187119137892172887 122750818780678706838259331)
              ·
                refine ⟨184126228171018060257388997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122750818780678706838259331 184126228171018060257388997)
                ·
                  refine ⟨34523667782065886298260437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184126228171018060257388997 34523667782065886298260437)
                  ·
                    refine ⟨809148463642169210115479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34523667782065886298260437 809148463642169210115479)
                    ·
                      rfl

theorem cell23_4727433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_4727433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727433 prefixEnd_4727433 := by exact prefixLift 4727433
  have htrace : WordTrace (prefixWord ++ tailWord_4727433) baseStart_4727433 baseEnd_4727433 := by
    simpa [prefixWord, tailWord_4727433, baseEnd_4727433] using wordTrace_append hprefix tailTrace_4727433
  have hstable : (prefixWord ++ tailWord_4727433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727433).length < 2 ^ (prefixWord ++ tailWord_4727433).sum := by decide
  have hdescent : baseEnd_4727433 < baseStart_4727433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727443 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 5]
def baseStart_4727443 : Nat := 118140960795 + 4727443 * 2 ^ 59
def prefixEnd_4727443 : Nat := 4983230072969 + 3 ^ 40 * 4727443 * 2
def baseEnd_4727443 : Nat := 2427450525733052591221391

theorem tailTrace_4727443 : CollatzResearch.WordTrace tailWord_4727443 prefixEnd_4727443 2427450525733052591221391 := by
  unfold tailWord_4727443
  simp only [CollatzResearch.WordTrace]
  refine ⟨172424011412288868830466983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114949340941525912553644655 172424011412288868830466983)
  ·
    refine ⟨258636017118433303245700475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172424011412288868830466983 258636017118433303245700475)
    ·
      refine ⟨387954025677649954868550713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258636017118433303245700475 387954025677649954868550713)
      ·
        refine ⟨290965519258237466151413035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387954025677649954868550713 290965519258237466151413035)
        ·
          refine ⟨436448278887356199227119553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290965519258237466151413035 436448278887356199227119553)
          ·
            refine ⟨327336209165517149420339665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436448278887356199227119553 327336209165517149420339665)
            ·
              refine ⟨245502156874137862065254749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327336209165517149420339665 245502156874137862065254749)
              ·
                refine ⟨92063308827801698274470531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245502156874137862065254749 92063308827801698274470531)
                ·
                  refine ⟨138094963241702547411705797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92063308827801698274470531 138094963241702547411705797)
                  ·
                    refine ⟨25892805607819227639694837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138094963241702547411705797 25892805607819227639694837)
                    ·
                      refine ⟨2427450525733052591221391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25892805607819227639694837 2427450525733052591221391)
                      ·
                        rfl

theorem cell23_4727443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_4727443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727443 prefixEnd_4727443 := by exact prefixLift 4727443
  have htrace : WordTrace (prefixWord ++ tailWord_4727443) baseStart_4727443 baseEnd_4727443 := by
    simpa [prefixWord, tailWord_4727443, baseEnd_4727443] using wordTrace_append hprefix tailTrace_4727443
  have hstable : (prefixWord ++ tailWord_4727443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727443).length < 2 ^ (prefixWord ++ tailWord_4727443).sum := by decide
  have hdescent : baseEnd_4727443 < baseStart_4727443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727447 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 3]
def baseStart_4727447 : Nat := 118140960795 + 4727447 * 2 ^ 59
def prefixEnd_4727447 : Nat := 4983230072969 + 3 ^ 40 * 4727447 * 2
def baseEnd_4727447 : Nat := 2427452579655670575571373

theorem tailTrace_4727447 : CollatzResearch.WordTrace tailWord_4727447 prefixEnd_4727447 2427452579655670575571373 := by
  unfold tailWord_4727447
  simp only [CollatzResearch.WordTrace]
  refine ⟨172424157304274377513612595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114949438202849585009075063 172424157304274377513612595)
  ·
    refine ⟨258636235956411566270418893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172424157304274377513612595 258636235956411566270418893)
    ·
      refine ⟨96988588483654337351407085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258636235956411566270418893 96988588483654337351407085)
      ·
        refine ⟨36370720681370376506777657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96988588483654337351407085 36370720681370376506777657)
        ·
          refine ⟨27278040511027782380083243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36370720681370376506777657 27278040511027782380083243)
          ·
            refine ⟨40917060766541673570124865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27278040511027782380083243 40917060766541673570124865)
            ·
              refine ⟨30687795574906255177593649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40917060766541673570124865 30687795574906255177593649)
              ·
                refine ⟨23015846681179691383195237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30687795574906255177593649 23015846681179691383195237)
                ·
                  refine ⟨4315471252721192134349107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23015846681179691383195237 4315471252721192134349107)
                  ·
                    refine ⟨6473206879081788201523661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4315471252721192134349107 6473206879081788201523661)
                    ·
                      refine ⟨2427452579655670575571373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6473206879081788201523661 2427452579655670575571373)
                      ·
                        rfl

theorem cell23_4727447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_4727447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727447 prefixEnd_4727447 := by exact prefixLift 4727447
  have htrace : WordTrace (prefixWord ++ tailWord_4727447) baseStart_4727447 baseEnd_4727447 := by
    simpa [prefixWord, tailWord_4727447, baseEnd_4727447] using wordTrace_append hprefix tailTrace_4727447
  have hstable : (prefixWord ++ tailWord_4727447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727447).length < 2 ^ (prefixWord ++ tailWord_4727447).sum := by decide
  have hdescent : baseEnd_4727447 < baseStart_4727447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727478 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_4727478 : Nat := 118140960795 + 4727478 * 2 ^ 59
def prefixEnd_4727478 : Nat := 4983230072969 + 3 ^ 40 * 4727478 * 2
def baseEnd_4727478 : Nat := 2427468497555959954283731

theorem tailTrace_4727478 : CollatzResearch.WordTrace tailWord_4727478 prefixEnd_4727478 2427468497555959954283731 := by
  unfold tailWord_4727478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10776580497947629362999443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114950191978108046538660725 10776580497947629362999443)
  ·
    refine ⟨16164870746921444044499165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10776580497947629362999443 16164870746921444044499165)
    ·
      refine ⟨6061826530095541516687187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16164870746921444044499165 6061826530095541516687187)
      ·
        refine ⟨9092739795143312275030781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6061826530095541516687187 9092739795143312275030781)
        ·
          refine ⟨3409777423178742103136543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9092739795143312275030781 3409777423178742103136543)
          ·
            refine ⟨5114666134768113154704815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409777423178742103136543 5114666134768113154704815)
            ·
              refine ⟨7671999202152169732057223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114666134768113154704815 7671999202152169732057223)
              ·
                refine ⟨11507998803228254598085835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7671999202152169732057223 11507998803228254598085835)
                ·
                  refine ⟨17261998204842381897128753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11507998803228254598085835 17261998204842381897128753)
                  ·
                    refine ⟨12946498653631786422846565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17261998204842381897128753 12946498653631786422846565)
                    ·
                      refine ⟨2427468497555959954283731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12946498653631786422846565 2427468497555959954283731)
                      ·
                        rfl

theorem cell23_4727478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_4727478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727478 prefixEnd_4727478 := by exact prefixLift 4727478
  have htrace : WordTrace (prefixWord ++ tailWord_4727478) baseStart_4727478 baseEnd_4727478 := by
    simpa [prefixWord, tailWord_4727478, baseEnd_4727478] using wordTrace_append hprefix tailTrace_4727478
  have hstable : (prefixWord ++ tailWord_4727478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727478).length < 2 ^ (prefixWord ++ tailWord_4727478).sum := by decide
  have hdescent : baseEnd_4727478 < baseStart_4727478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727538 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_4727538 : Nat := 118140960795 + 4727538 * 2 ^ 59
def prefixEnd_4727538 : Nat := 4983230072969 + 3 ^ 40 * 4727538 * 2
def baseEnd_4727538 : Nat := 2427499306395229719533455

theorem tailTrace_4727538 : CollatzResearch.WordTrace tailWord_4727538 prefixEnd_4727538 2427499306395229719533455 := by
  unfold tailWord_4727538
  simp only [CollatzResearch.WordTrace]
  refine ⟨43106869086736175013793817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114951650897963133370116845 43106869086736175013793817)
  ·
    refine ⟨32330151815052131260345363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43106869086736175013793817 32330151815052131260345363)
    ·
      refine ⟨48495227722578196890518045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32330151815052131260345363 48495227722578196890518045)
      ·
        refine ⟨18185710395966823833944267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48495227722578196890518045 18185710395966823833944267)
        ·
          refine ⟨27278565593950235750916401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18185710395966823833944267 27278565593950235750916401)
          ·
            refine ⟨20458924195462676813187301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27278565593950235750916401 20458924195462676813187301)
            ·
              refine ⟨3836048286649251902472619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20458924195462676813187301 3836048286649251902472619)
              ·
                refine ⟨5754072429973877853708929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3836048286649251902472619 5754072429973877853708929)
                ·
                  refine ⟨4315554322480408390281697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5754072429973877853708929 4315554322480408390281697)
                  ·
                    refine ⟨3236665741860306292711273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4315554322480408390281697 3236665741860306292711273)
                    ·
                      refine ⟨2427499306395229719533455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3236665741860306292711273 2427499306395229719533455)
                      ·
                        rfl

theorem cell23_4727538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_4727538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727538 prefixEnd_4727538 := by exact prefixLift 4727538
  have htrace : WordTrace (prefixWord ++ tailWord_4727538) baseStart_4727538 baseEnd_4727538 := by
    simpa [prefixWord, tailWord_4727538, baseEnd_4727538] using wordTrace_append hprefix tailTrace_4727538
  have hstable : (prefixWord ++ tailWord_4727538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727538).length < 2 ^ (prefixWord ++ tailWord_4727538).sum := by decide
  have hdescent : baseEnd_4727538 < baseStart_4727538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727587 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 3, 4]
def baseStart_4727587 : Nat := 118140960795 + 4727587 * 2 ^ 59
def prefixEnd_4727587 : Nat := 4983230072969 + 3 ^ 40 * 4727587 * 2
def baseEnd_4727587 : Nat := 809174822315766675940243

theorem tailTrace_4727587 : CollatzResearch.WordTrace tailWord_4727587 prefixEnd_4727587 809174822315766675940243 := by
  unfold tailWord_4727587
  simp only [CollatzResearch.WordTrace]
  refine ⟨172429263523767181423709015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114952842349178120949139343 172429263523767181423709015)
  ·
    refine ⟨258643895285650772135563523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172429263523767181423709015 258643895285650772135563523)
    ·
      refine ⟨387965842928476158203345285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258643895285650772135563523 387965842928476158203345285)
      ·
        refine ⟨72743595549089279663127241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 387965842928476158203345285 72743595549089279663127241)
        ·
          refine ⟨54557696661816959747345431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72743595549089279663127241 54557696661816959747345431)
          ·
            refine ⟨81836544992725439621018147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54557696661816959747345431 81836544992725439621018147)
            ·
              refine ⟨122754817489088159431527221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81836544992725439621018147 122754817489088159431527221)
              ·
                refine ⟨11508264139602014946705677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122754817489088159431527221 11508264139602014946705677)
                ·
                  refine ⟨4315599052350755605014629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11508264139602014946705677 4315599052350755605014629)
                  ·
                    refine ⟨809174822315766675940243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315599052350755605014629 809174822315766675940243)
                    ·
                      rfl

theorem cell23_4727587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 4].length) (baseStart_4727587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727587 prefixEnd_4727587 := by exact prefixLift 4727587
  have htrace : WordTrace (prefixWord ++ tailWord_4727587) baseStart_4727587 baseEnd_4727587 := by
    simpa [prefixWord, tailWord_4727587, baseEnd_4727587] using wordTrace_append hprefix tailTrace_4727587
  have hstable : (prefixWord ++ tailWord_4727587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727587).length < 2 ^ (prefixWord ++ tailWord_4727587).sum := by decide
  have hdescent : baseEnd_4727587 < baseStart_4727587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727667 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 4]
def baseStart_4727667 : Nat := 118140960795 + 4727667 * 2 ^ 59
def prefixEnd_4727667 : Nat := 4983230072969 + 3 ^ 40 * 4727667 * 2
def baseEnd_4727667 : Nat := 2427565545399659714820361

theorem tailTrace_4727667 : CollatzResearch.WordTrace tailWord_4727667 prefixEnd_4727667 2427565545399659714820361 := by
  unfold tailWord_4727667
  simp only [CollatzResearch.WordTrace]
  refine ⟨172432181363477355086621255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114954787575651570057747503 172432181363477355086621255)
  ·
    refine ⟨258648272045216032629931883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172432181363477355086621255 258648272045216032629931883)
    ·
      refine ⟨387972408067824048944897825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258648272045216032629931883 387972408067824048944897825)
      ·
        refine ⟨290979306050868036708673369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387972408067824048944897825 290979306050868036708673369)
        ·
          refine ⟨218234479538151027531505027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290979306050868036708673369 218234479538151027531505027)
          ·
            refine ⟨327351719307226541297257541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218234479538151027531505027 327351719307226541297257541)
            ·
              refine ⟨61378447370104976493235789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327351719307226541297257541 61378447370104976493235789)
              ·
                refine ⟨23016917763789366184963421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61378447370104976493235789 23016917763789366184963421)
                ·
                  refine ⟨8631344161421012319361283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23016917763789366184963421 8631344161421012319361283)
                  ·
                    refine ⟨12947016242131518479041925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8631344161421012319361283 12947016242131518479041925)
                    ·
                      refine ⟨2427565545399659714820361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12947016242131518479041925 2427565545399659714820361)
                      ·
                        rfl

theorem cell23_4727667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_4727667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727667 prefixEnd_4727667 := by exact prefixLift 4727667
  have htrace : WordTrace (prefixWord ++ tailWord_4727667) baseStart_4727667 baseEnd_4727667 := by
    simpa [prefixWord, tailWord_4727667, baseEnd_4727667] using wordTrace_append hprefix tailTrace_4727667
  have hstable : (prefixWord ++ tailWord_4727667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727667).length < 2 ^ (prefixWord ++ tailWord_4727667).sum := by decide
  have hdescent : baseEnd_4727667 < baseStart_4727667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727677 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_4727677 : Nat := 118140960795 + 4727677 * 2 ^ 59
def prefixEnd_4727677 : Nat := 4983230072969 + 3 ^ 40 * 4727677 * 2
def baseEnd_4727677 : Nat := 809190226735401558565105

theorem tailTrace_4727677 : CollatzResearch.WordTrace tailWord_4727677 prefixEnd_4727677 809190226735401558565105 := by
  unfold tailWord_4727677
  simp only [CollatzResearch.WordTrace]
  refine ⟨172432546093441126794485285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114955030728960751196323523 172432546093441126794485285)
  ·
    refine ⟨32331102392520211273965991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172432546093441126794485285 32331102392520211273965991)
    ·
      refine ⟨48496653588780316910948987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32331102392520211273965991 48496653588780316910948987)
      ·
        refine ⟨72744980383170475366423481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48496653588780316910948987 72744980383170475366423481)
        ·
          refine ⟨54558735287377856524817611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72744980383170475366423481 54558735287377856524817611)
          ·
            refine ⟨81838102931066784787226417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54558735287377856524817611 81838102931066784787226417)
            ·
              refine ⟨61378577198300088590419813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81838102931066784787226417 61378577198300088590419813)
              ·
                refine ⟨11508483224681266610703715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61378577198300088590419813 11508483224681266610703715)
                ·
                  refine ⟨17262724837021899916055573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11508483224681266610703715 17262724837021899916055573)
                  ·
                    refine ⟨809190226735401558565105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17262724837021899916055573 809190226735401558565105)
                    ·
                      rfl

theorem cell23_4727677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_4727677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727677 prefixEnd_4727677 := by exact prefixLift 4727677
  have htrace : WordTrace (prefixWord ++ tailWord_4727677) baseStart_4727677 baseEnd_4727677 := by
    simpa [prefixWord, tailWord_4727677, baseEnd_4727677] using wordTrace_append hprefix tailTrace_4727677
  have hstable : (prefixWord ++ tailWord_4727677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727677).length < 2 ^ (prefixWord ++ tailWord_4727677).sum := by decide
  have hdescent : baseEnd_4727677 < baseStart_4727677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727711 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 2, 4]
def baseStart_4727711 : Nat := 118140960795 + 4727711 * 2 ^ 59
def prefixEnd_4727711 : Nat := 4983230072969 + 3 ^ 40 * 4727711 * 2
def baseEnd_4727711 : Nat := 809196046182819180890053

theorem tailTrace_4727711 : CollatzResearch.WordTrace tailWord_4727711 prefixEnd_4727711 809196046182819180890053 := by
  unfold tailWord_4727711
  simp only [CollatzResearch.WordTrace]
  refine ⟨172433786175317950601222987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114955857450211967067481991 172433786175317950601222987)
  ·
    refine ⟨258650679262976925901834481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172433786175317950601222987 258650679262976925901834481)
    ·
      refine ⟨193988009447232694426375861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258650679262976925901834481 193988009447232694426375861)
      ·
        refine ⟨18186375885678065102472737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193988009447232694426375861 18186375885678065102472737)
        ·
          refine ⟨13639781914258548826854553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18186375885678065102472737 13639781914258548826854553)
          ·
            refine ⟨10229836435693911620140915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13639781914258548826854553 10229836435693911620140915)
            ·
              refine ⟨15344754653540867430211373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10229836435693911620140915 15344754653540867430211373)
              ·
                refine ⟨5754282995077825286329265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15344754653540867430211373 5754282995077825286329265)
                ·
                  refine ⟨4315712246308368964746949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5754282995077825286329265 4315712246308368964746949)
                  ·
                    refine ⟨809196046182819180890053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315712246308368964746949 809196046182819180890053)
                    ·
                      rfl

theorem cell23_4727711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 4].length) (baseStart_4727711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727711 prefixEnd_4727711 := by exact prefixLift 4727711
  have htrace : WordTrace (prefixWord ++ tailWord_4727711) baseStart_4727711 baseEnd_4727711 := by
    simpa [prefixWord, tailWord_4727711, baseEnd_4727711] using wordTrace_append hprefix tailTrace_4727711
  have hstable : (prefixWord ++ tailWord_4727711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727711).length < 2 ^ (prefixWord ++ tailWord_4727711).sum := by decide
  have hdescent : baseEnd_4727711 < baseStart_4727711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727714 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_4727714 : Nat := 118140960795 + 4727714 * 2 ^ 59
def prefixEnd_4727714 : Nat := 4983230072969 + 3 ^ 40 * 4727714 * 2
def baseEnd_4727714 : Nat := 2427589678990421030932645

theorem tailTrace_4727714 : CollatzResearch.WordTrace tailWord_4727714 prefixEnd_4727714 2427589678990421030932645 := by
  unfold tailWord_4727714
  simp only [CollatzResearch.WordTrace]
  refine ⟨43108473898576770528395549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114955930396204721409054797 43108473898576770528395549)
  ·
    refine ⟨16165677711966288948148331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43108473898576770528395549 16165677711966288948148331)
    ·
      refine ⟨24248516567949433422222497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16165677711966288948148331 24248516567949433422222497)
      ·
        refine ⟨18186387425962075066666873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24248516567949433422222497 18186387425962075066666873)
        ·
          refine ⟨13639790569471556300000155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18186387425962075066666873 13639790569471556300000155)
          ·
            refine ⟨20459685854207334450000233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13639790569471556300000155 20459685854207334450000233)
            ·
              refine ⟨15344764390655500837500175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20459685854207334450000233 15344764390655500837500175)
              ·
                refine ⟨23017146585983251256250263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15344764390655500837500175 23017146585983251256250263)
                ·
                  refine ⟨34525719878974876884375395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23017146585983251256250263 34525719878974876884375395)
                  ·
                    refine ⟨51788579818462315326563093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34525719878974876884375395 51788579818462315326563093)
                    ·
                      refine ⟨2427589678990421030932645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51788579818462315326563093 2427589678990421030932645)
                      ·
                        rfl

theorem cell23_4727714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_4727714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727714 prefixEnd_4727714 := by exact prefixLift 4727714
  have htrace : WordTrace (prefixWord ++ tailWord_4727714) baseStart_4727714 baseEnd_4727714 := by
    simpa [prefixWord, tailWord_4727714, baseEnd_4727714] using wordTrace_append hprefix tailTrace_4727714
  have hstable : (prefixWord ++ tailWord_4727714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727714).length < 2 ^ (prefixWord ++ tailWord_4727714).sum := by decide
  have hdescent : baseEnd_4727714 < baseStart_4727714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727751 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_4727751 : Nat := 118140960795 + 4727751 * 2 ^ 59
def prefixEnd_4727751 : Nat := 4983230072969 + 3 ^ 40 * 4727751 * 2
def baseEnd_4727751 : Nat := 2427608677774637386169975

theorem tailTrace_4727751 : CollatzResearch.WordTrace tailWord_4727751 prefixEnd_4727751 2427608677774637386169975 := by
  unfold tailWord_4727751
  simp only [CollatzResearch.WordTrace]
  refine ⟨172435245095173037432679107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114956830063448691621786071 172435245095173037432679107)
  ·
    refine ⟨258652867642759556149018661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172435245095173037432679107 258652867642759556149018661)
    ·
      refine ⟨48497412683017416777940999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258652867642759556149018661 48497412683017416777940999)
      ·
        refine ⟨72746119024526125166911499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48497412683017416777940999 72746119024526125166911499)
        ·
          refine ⟨109119178536789187750367249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72746119024526125166911499 109119178536789187750367249)
          ·
            refine ⟨81839383902591890812775437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109119178536789187750367249 81839383902591890812775437)
            ·
              refine ⟨30689768963471959054790789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81839383902591890812775437 30689768963471959054790789)
              ·
                refine ⟨5754331680650992322773273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30689768963471959054790789 5754331680650992322773273)
                ·
                  refine ⟨4315748760488244242079955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5754331680650992322773273 4315748760488244242079955)
                  ·
                    refine ⟨6473623140732366363119933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4315748760488244242079955 6473623140732366363119933)
                    ·
                      refine ⟨2427608677774637386169975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6473623140732366363119933 2427608677774637386169975)
                      ·
                        rfl

theorem cell23_4727751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_4727751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727751 prefixEnd_4727751 := by exact prefixLift 4727751
  have htrace : WordTrace (prefixWord ++ tailWord_4727751) baseStart_4727751 baseEnd_4727751 := by
    simpa [prefixWord, tailWord_4727751, baseEnd_4727751] using wordTrace_append hprefix tailTrace_4727751
  have hstable : (prefixWord ++ tailWord_4727751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727751).length < 2 ^ (prefixWord ++ tailWord_4727751).sum := by decide
  have hdescent : baseEnd_4727751 < baseStart_4727751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727791 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 1, 4, 2]
def baseStart_4727791 : Nat := 118140960795 + 4727791 * 2 ^ 59
def prefixEnd_4727791 : Nat := 4983230072969 + 3 ^ 40 * 4727791 * 2
def baseEnd_4727791 : Nat := 2427629217000817229669791

theorem tailTrace_4727791 : CollatzResearch.WordTrace tailWord_4727791 prefixEnd_4727791 2427629217000817229669791 := by
  unfold tailWord_4727791
  simp only [CollatzResearch.WordTrace]
  refine ⟨172436704015028124264135227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114957802676685416176090151 172436704015028124264135227)
  ·
    refine ⟨258655056022542186396202841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172436704015028124264135227 258655056022542186396202841)
    ·
      refine ⟨193991292016906639797152131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258655056022542186396202841 193991292016906639797152131)
      ·
        refine ⟨290986938025359959695728197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193991292016906639797152131 290986938025359959695728197)
        ·
          refine ⟨54560050879754992442949037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 290986938025359959695728197 54560050879754992442949037)
          ·
            refine ⟨20460019079908122166105889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54560050879754992442949037 20460019079908122166105889)
            ·
              refine ⟨15345014309931091624579417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20460019079908122166105889 15345014309931091624579417)
              ·
                refine ⟨11508760732448318718434563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15345014309931091624579417 11508760732448318718434563)
                ·
                  refine ⟨17263141098672478077651845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11508760732448318718434563 17263141098672478077651845)
                  ·
                    refine ⟨3236838956001089639559721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17263141098672478077651845 3236838956001089639559721)
                    ·
                      refine ⟨2427629217000817229669791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3236838956001089639559721 2427629217000817229669791)
                      ·
                        rfl

theorem cell23_4727791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 4, 2].length) (baseStart_4727791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727791 prefixEnd_4727791 := by exact prefixLift 4727791
  have htrace : WordTrace (prefixWord ++ tailWord_4727791) baseStart_4727791 baseEnd_4727791 := by
    simpa [prefixWord, tailWord_4727791, baseEnd_4727791] using wordTrace_append hprefix tailTrace_4727791
  have hstable : (prefixWord ++ tailWord_4727791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727791).length < 2 ^ (prefixWord ++ tailWord_4727791).sum := by decide
  have hdescent : baseEnd_4727791 < baseStart_4727791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727796 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4727796 : Nat := 118140960795 + 4727796 * 2 ^ 59
def prefixEnd_4727796 : Nat := 4983230072969 + 3 ^ 40 * 4727796 * 2
def baseEnd_4727796 : Nat := 809210594801363236702423

theorem tailTrace_4727796 : CollatzResearch.WordTrace tailWord_4727796 prefixEnd_4727796 809210594801363236702423 := by
  unfold tailWord_4727796
  simp only [CollatzResearch.WordTrace]
  refine ⟨86218443190005005059033621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114957924253340006745378161 86218443190005005059033621)
  ·
    refine ⟨4041489524531484612142201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86218443190005005059033621 4041489524531484612142201)
    ·
      refine ⟨3031117143398613459106651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4041489524531484612142201 3031117143398613459106651)
      ·
        refine ⟨4546675715097920188659977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3031117143398613459106651 4546675715097920188659977)
        ·
          refine ⟨3410006786323440141494983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4546675715097920188659977 3410006786323440141494983)
          ·
            refine ⟨5115010179485160212242475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410006786323440141494983 5115010179485160212242475)
            ·
              refine ⟨7672515269227740318363713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5115010179485160212242475 7672515269227740318363713)
              ·
                refine ⟨5754386451920805238772785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7672515269227740318363713 5754386451920805238772785)
                ·
                  refine ⟨4315789838940603929079589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5754386451920805238772785 4315789838940603929079589)
                  ·
                    refine ⟨809210594801363236702423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315789838940603929079589 809210594801363236702423)
                    ·
                      rfl

theorem cell23_4727796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4727796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727796 prefixEnd_4727796 := by exact prefixLift 4727796
  have htrace : WordTrace (prefixWord ++ tailWord_4727796) baseStart_4727796 baseEnd_4727796 := by
    simpa [prefixWord, tailWord_4727796, baseEnd_4727796] using wordTrace_append hprefix tailTrace_4727796
  have hstable : (prefixWord ++ tailWord_4727796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727796).length < 2 ^ (prefixWord ++ tailWord_4727796).sum := by decide
  have hdescent : baseEnd_4727796 < baseStart_4727796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727804 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_4727804 : Nat := 118140960795 + 4727804 * 2 ^ 59
def prefixEnd_4727804 : Nat := 4983230072969 + 3 ^ 40 * 4727804 * 2
def baseEnd_4727804 : Nat := 2427635892249325678807231

theorem tailTrace_4727804 : CollatzResearch.WordTrace tailWord_4727804 prefixEnd_4727804 2427635892249325678807231 := by
  unfold tailWord_4727804
  simp only [CollatzResearch.WordTrace]
  refine ⟨86218589081990513742179233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114958118775987351656238977 86218589081990513742179233)
  ·
    refine ⟨64663941811492885306634425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86218589081990513742179233 64663941811492885306634425)
    ·
      refine ⟨48497956358619663979975819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64663941811492885306634425 48497956358619663979975819)
      ·
        refine ⟨72746934537929495969963729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48497956358619663979975819 72746934537929495969963729)
        ·
          refine ⟨54560200903447121977472797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72746934537929495969963729 54560200903447121977472797)
          ·
            refine ⟨20460075338792670741552299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54560200903447121977472797 20460075338792670741552299)
            ·
              refine ⟨30690113008189006112328449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20460075338792670741552299 30690113008189006112328449)
              ·
                refine ⟨23017584756141754584246337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30690113008189006112328449 23017584756141754584246337)
                ·
                  refine ⟨17263188567106315938184753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23017584756141754584246337 17263188567106315938184753)
                  ·
                    refine ⟨12947391425329736953638565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17263188567106315938184753 12947391425329736953638565)
                    ·
                      refine ⟨2427635892249325678807231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12947391425329736953638565 2427635892249325678807231)
                      ·
                        rfl

theorem cell23_4727804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_4727804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727804 prefixEnd_4727804 := by exact prefixLift 4727804
  have htrace : WordTrace (prefixWord ++ tailWord_4727804) baseStart_4727804 baseEnd_4727804 := by
    simpa [prefixWord, tailWord_4727804, baseEnd_4727804] using wordTrace_append hprefix tailTrace_4727804
  have hstable : (prefixWord ++ tailWord_4727804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727804).length < 2 ^ (prefixWord ++ tailWord_4727804).sum := by decide
  have hdescent : baseEnd_4727804 < baseStart_4727804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727908 : List Nat := [2, 3, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_4727908 : Nat := 118140960795 + 4727908 * 2 ^ 59
def prefixEnd_4727908 : Nat := 4983230072969 + 3 ^ 40 * 4727908 * 2
def baseEnd_4727908 : Nat := 809229764745797757302251

theorem tailTrace_4727908 : CollatzResearch.WordTrace tailWord_4727908 prefixEnd_4727908 809229764745797757302251 := by
  unfold tailWord_4727908
  simp only [CollatzResearch.WordTrace]
  refine ⟨86220485677802126623072189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114960647570402835497429585 86220485677802126623072189)
  ·
    refine ⟨32332682129175797483652071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86220485677802126623072189 32332682129175797483652071)
    ·
      refine ⟨48499023193763696225478107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32332682129175797483652071 48499023193763696225478107)
      ·
        refine ⟨72748534790645544338217161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48499023193763696225478107 72748534790645544338217161)
        ·
          refine ⟨54561401092984158253662871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72748534790645544338217161 54561401092984158253662871)
          ·
            refine ⟨81842101639476237380494307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54561401092984158253662871 81842101639476237380494307)
            ·
              refine ⟨122763152459214356070741461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81842101639476237380494307 122763152459214356070741461)
              ·
                refine ⟨2877261385762836470408003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 122763152459214356070741461 2877261385762836470408003)
                ·
                  refine ⟨4315892078644254705612005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877261385762836470408003 4315892078644254705612005)
                  ·
                    refine ⟨809229764745797757302251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4315892078644254705612005 809229764745797757302251)
                    ·
                      rfl

theorem cell23_4727908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_4727908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727908 prefixEnd_4727908 := by exact prefixLift 4727908
  have htrace : WordTrace (prefixWord ++ tailWord_4727908) baseStart_4727908 baseEnd_4727908 := by
    simpa [prefixWord, tailWord_4727908, baseEnd_4727908] using wordTrace_append hprefix tailTrace_4727908
  have hstable : (prefixWord ++ tailWord_4727908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727908).length < 2 ^ (prefixWord ++ tailWord_4727908).sum := by decide
  have hdescent : baseEnd_4727908 < baseStart_4727908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727918 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_4727918 : Nat := 118140960795 + 4727918 * 2 ^ 59
def prefixEnd_4727918 : Nat := 4983230072969 + 3 ^ 40 * 4727918 * 2
def baseEnd_4727918 : Nat := 2427694429043938232781707

theorem tailTrace_4727918 : CollatzResearch.WordTrace tailWord_4727918 prefixEnd_4727918 2427694429043938232781707 := by
  unfold tailWord_4727918
  simp only [CollatzResearch.WordTrace]
  refine ⟨21555167010696003119251051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114960890723712016636005605 21555167010696003119251051)
  ·
    refine ⟨32332750516044004678876577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21555167010696003119251051 32332750516044004678876577)
    ·
      refine ⟨24249562887033003509157433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32332750516044004678876577 24249562887033003509157433)
      ·
        refine ⟨18187172165274752631868075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24249562887033003509157433 18187172165274752631868075)
        ·
          refine ⟨27280758247912128947802113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18187172165274752631868075 27280758247912128947802113)
          ·
            refine ⟨20460568685934096710851585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27280758247912128947802113 20460568685934096710851585)
            ·
              refine ⟨15345426514450572533138689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20460568685934096710851585 15345426514450572533138689)
              ·
                refine ⟨11509069885837929399854017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15345426514450572533138689 11509069885837929399854017)
                ·
                  refine ⟨8631802414378447049890513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11509069885837929399854017 8631802414378447049890513)
                  ·
                    refine ⟨6473851810783835287417885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8631802414378447049890513 6473851810783835287417885)
                    ·
                      refine ⟨2427694429043938232781707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6473851810783835287417885 2427694429043938232781707)
                      ·
                        rfl

theorem cell23_4727918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_4727918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727918 prefixEnd_4727918 := by exact prefixLift 4727918
  have htrace : WordTrace (prefixWord ++ tailWord_4727918) baseStart_4727918 baseEnd_4727918 := by
    simpa [prefixWord, tailWord_4727918, baseEnd_4727918] using wordTrace_append hprefix tailTrace_4727918
  have hstable : (prefixWord ++ tailWord_4727918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727918).length < 2 ^ (prefixWord ++ tailWord_4727918).sum := by decide
  have hdescent : baseEnd_4727918 < baseStart_4727918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727931 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 3]
def baseStart_4727931 : Nat := 118140960795 + 4727931 * 2 ^ 59
def prefixEnd_4727931 : Nat := 4983230072969 + 3 ^ 40 * 4727931 * 2
def baseEnd_4727931 : Nat := 2427701104292446681919147

theorem tailTrace_4727931 : CollatzResearch.WordTrace tailWord_4727931 prefixEnd_4727931 2427701104292446681919147 := by
  unfold tailWord_4727931
  simp only [CollatzResearch.WordTrace]
  refine ⟨172441810234520928174231647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114961206823013952116154431 172441810234520928174231647)
  ·
    refine ⟨258662715351781392261347471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172441810234520928174231647 258662715351781392261347471)
    ·
      refine ⟨387994073027672088392021207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258662715351781392261347471 387994073027672088392021207)
      ·
        refine ⟨581991109541508132588031811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387994073027672088392021207 581991109541508132588031811)
        ·
          refine ⟨872986664312262198882047717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581991109541508132588031811 872986664312262198882047717)
          ·
            refine ⟨163684999558549162290383947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 872986664312262198882047717 163684999558549162290383947)
            ·
              refine ⟨245527499337823743435575921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163684999558549162290383947 245527499337823743435575921)
              ·
                refine ⟨184145624503367807576681941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245527499337823743435575921 184145624503367807576681941)
                ·
                  refine ⟨4315913074297682990078483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 184145624503367807576681941 4315913074297682990078483)
                  ·
                    refine ⟨6473869611446524485117725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4315913074297682990078483 6473869611446524485117725)
                    ·
                      refine ⟨2427701104292446681919147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6473869611446524485117725 2427701104292446681919147)
                      ·
                        rfl

theorem cell23_4727931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 3].length) (baseStart_4727931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727931 prefixEnd_4727931 := by exact prefixLift 4727931
  have htrace : WordTrace (prefixWord ++ tailWord_4727931) baseStart_4727931 baseEnd_4727931 := by
    simpa [prefixWord, tailWord_4727931, baseEnd_4727931] using wordTrace_append hprefix tailTrace_4727931
  have hstable : (prefixWord ++ tailWord_4727931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727931).length < 2 ^ (prefixWord ++ tailWord_4727931).sum := by decide
  have hdescent : baseEnd_4727931 < baseStart_4727931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727971 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 1, 8, 2]
def baseStart_4727971 : Nat := 118140960795 + 4727971 * 2 ^ 59
def prefixEnd_4727971 : Nat := 4983230072969 + 3 ^ 40 * 4727971 * 2
def baseEnd_4727971 : Nat := 2427721643518626525418963

theorem tailTrace_4727971 : CollatzResearch.WordTrace tailWord_4727971 prefixEnd_4727971 2427721643518626525418963 := by
  unfold tailWord_4727971
  simp only [CollatzResearch.WordTrace]
  refine ⟨172443269154376015005687767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114962179436250676670458511 172443269154376015005687767)
  ·
    refine ⟨258664903731564022508531651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172443269154376015005687767 258664903731564022508531651)
    ·
      refine ⟨387997355597346033762797477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258664903731564022508531651 387997355597346033762797477)
      ·
        refine ⟨72749504174502381330524527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 387997355597346033762797477 72749504174502381330524527)
        ·
          refine ⟨109124256261753571995786791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72749504174502381330524527 109124256261753571995786791)
          ·
            refine ⟨163686384392630357993680187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109124256261753571995786791 163686384392630357993680187)
            ·
              refine ⟨245529576588945536990520281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163686384392630357993680187 245529576588945536990520281)
              ·
                refine ⟨184147182441709152742890211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245529576588945536990520281 184147182441709152742890211)
                ·
                  refine ⟨276220773662563729114335317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184147182441709152742890211 276220773662563729114335317)
                  ·
                    refine ⟨3236962191358168700558617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 276220773662563729114335317 3236962191358168700558617)
                    ·
                      refine ⟨2427721643518626525418963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3236962191358168700558617 2427721643518626525418963)
                      ·
                        rfl

theorem cell23_4727971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_4727971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727971 prefixEnd_4727971 := by exact prefixLift 4727971
  have htrace : WordTrace (prefixWord ++ tailWord_4727971) baseStart_4727971 baseEnd_4727971 := by
    simpa [prefixWord, tailWord_4727971, baseEnd_4727971] using wordTrace_append hprefix tailTrace_4727971
  have hstable : (prefixWord ++ tailWord_4727971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727971).length < 2 ^ (prefixWord ++ tailWord_4727971).sum := by decide
  have hdescent : baseEnd_4727971 < baseStart_4727971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727984 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_4727984 : Nat := 118140960795 + 4727984 * 2 ^ 59
def prefixEnd_4727984 : Nat := 4983230072969 + 3 ^ 40 * 4727984 * 2
def baseEnd_4727984 : Nat := 2427728318767134974556403

theorem tailTrace_4727984 : CollatzResearch.WordTrace tailWord_4727984 prefixEnd_4727984 2427728318767134974556403 := by
  unfold tailWord_4727984
  simp only [CollatzResearch.WordTrace]
  refine ⟨86221871651664459112955503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114962495535552612150607337 86221871651664459112955503)
  ·
    refine ⟨129332807477496688669433255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86221871651664459112955503 129332807477496688669433255)
    ·
      refine ⟨193999211216245033004149883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129332807477496688669433255 193999211216245033004149883)
      ·
        refine ⟨290998816824367549506224825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193999211216245033004149883 290998816824367549506224825)
        ·
          refine ⟨218249112618275662129668619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290998816824367549506224825 218249112618275662129668619)
          ·
            refine ⟨327373668927413493194502929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218249112618275662129668619 327373668927413493194502929)
            ·
              refine ⟨245530251695560119895877197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327373668927413493194502929 245530251695560119895877197)
              ·
                refine ⟨92073844385835044960953949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245530251695560119895877197 92073844385835044960953949)
                ·
                  refine ⟨34527691644688141860357731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92073844385835044960953949 34527691644688141860357731)
                  ·
                    refine ⟨51791537467032212790536597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34527691644688141860357731 51791537467032212790536597)
                    ·
                      refine ⟨2427728318767134974556403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51791537467032212790536597 2427728318767134974556403)
                      ·
                        rfl

theorem cell23_4727984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_4727984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727984 prefixEnd_4727984 := by exact prefixLift 4727984
  have htrace : WordTrace (prefixWord ++ tailWord_4727984) baseStart_4727984 baseEnd_4727984 := by
    simpa [prefixWord, tailWord_4727984, baseEnd_4727984] using wordTrace_append hprefix tailTrace_4727984
  have hstable : (prefixWord ++ tailWord_4727984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727984).length < 2 ^ (prefixWord ++ tailWord_4727984).sum := by decide
  have hdescent : baseEnd_4727984 < baseStart_4727984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727991 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_4727991 : Nat := 118140960795 + 4727991 * 2 ^ 59
def prefixEnd_4727991 : Nat := 4983230072969 + 3 ^ 40 * 4727991 * 2
def baseEnd_4727991 : Nat := 2427731913131716447168871

theorem tailTrace_4727991 : CollatzResearch.WordTrace tailWord_4727991 prefixEnd_4727991 2427731913131716447168871 := by
  unfold tailWord_4727991
  simp only [CollatzResearch.WordTrace]
  refine ⟨172443998614303558421415827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114962665742869038947610551 172443998614303558421415827)
  ·
    refine ⟨258665997921455337632123741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172443998614303558421415827 258665997921455337632123741)
    ·
      refine ⟨96999749220545751612046403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258665997921455337632123741 96999749220545751612046403)
      ·
        refine ⟨145499623830818627418069605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96999749220545751612046403 145499623830818627418069605)
        ·
          refine ⟨27281179468278492640888051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145499623830818627418069605 27281179468278492640888051)
          ·
            refine ⟨40921769202417738961332077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27281179468278492640888051 40921769202417738961332077)
            ·
              refine ⟨15345663450906652110499529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40921769202417738961332077 15345663450906652110499529)
              ·
                refine ⟨11509247588179989082874647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15345663450906652110499529 11509247588179989082874647)
                ·
                  refine ⟨17263871382269983624311971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11509247588179989082874647 17263871382269983624311971)
                  ·
                    refine ⟨25895807073404975436467957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17263871382269983624311971 25895807073404975436467957)
                    ·
                      refine ⟨2427731913131716447168871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25895807073404975436467957 2427731913131716447168871)
                      ·
                        rfl

theorem cell23_4727991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_4727991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727991 prefixEnd_4727991 := by exact prefixLift 4727991
  have htrace : WordTrace (prefixWord ++ tailWord_4727991) baseStart_4727991 baseEnd_4727991 := by
    simpa [prefixWord, tailWord_4727991, baseEnd_4727991] using wordTrace_append hprefix tailTrace_4727991
  have hstable : (prefixWord ++ tailWord_4727991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727991).length < 2 ^ (prefixWord ++ tailWord_4727991).sum := by decide
  have hdescent : baseEnd_4727991 < baseStart_4727991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727994 : List Nat := [3, 1, 1, 1, 2, 2, 1, 12]
def baseStart_4727994 : Nat := 118140960795 + 4727994 * 2 ^ 59
def prefixEnd_4727994 : Nat := 4983230072969 + 3 ^ 40 * 4727994 * 2
def baseEnd_4727994 : Nat := 89916053836062219830791

theorem tailTrace_4727994 : CollatzResearch.WordTrace tailWord_4727994 prefixEnd_4727994 89916053836062219830791 := by
  unfold tailWord_4727994
  simp only [CollatzResearch.WordTrace]
  refine ⟨43111027008323172483443759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114962738688861793289183357 43111027008323172483443759)
  ·
    refine ⟨64666540512484758725165639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43111027008323172483443759 64666540512484758725165639)
    ·
      refine ⟨96999810768727138087748459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64666540512484758725165639 96999810768727138087748459)
      ·
        refine ⟨145499716153090707131622689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96999810768727138087748459 145499716153090707131622689)
        ·
          refine ⟨109124787114818030348717017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145499716153090707131622689 109124787114818030348717017)
          ·
            refine ⟨81843590336113522761537763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109124787114818030348717017 81843590336113522761537763)
            ·
              refine ⟨122765385504170284142306645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81843590336113522761537763 122765385504170284142306645)
              ·
                refine ⟨89916053836062219830791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 122765385504170284142306645 89916053836062219830791)
                ·
                  rfl

theorem cell23_4727994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 12].length) (baseStart_4727994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727994 prefixEnd_4727994 := by exact prefixLift 4727994
  have htrace : WordTrace (prefixWord ++ tailWord_4727994) baseStart_4727994 baseEnd_4727994 := by
    simpa [prefixWord, tailWord_4727994, baseEnd_4727994] using wordTrace_append hprefix tailTrace_4727994
  have hstable : (prefixWord ++ tailWord_4727994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727994).length < 2 ^ (prefixWord ++ tailWord_4727994).sum := by decide
  have hdescent : baseEnd_4727994 < baseStart_4727994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4727998 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_4727998 : Nat := 118140960795 + 4727998 * 2 ^ 59
def prefixEnd_4727998 : Nat := 4983230072969 + 3 ^ 40 * 4727998 * 2
def baseEnd_4727998 : Nat := 809245169165432639927113

theorem tailTrace_4727998 : CollatzResearch.WordTrace tailWord_4727998 prefixEnd_4727998 809245169165432639927113 := by
  unfold tailWord_4727998
  simp only [CollatzResearch.WordTrace]
  refine ⟨21555531740659774827115081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114962835950185465744613765 21555531740659774827115081)
  ·
    refine ⟨16166648805494831120336311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21555531740659774827115081 16166648805494831120336311)
    ·
      refine ⟨24249973208242246680504467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16166648805494831120336311 24249973208242246680504467)
      ·
        refine ⟨36374959812363370020756701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24249973208242246680504467 36374959812363370020756701)
        ·
          refine ⟨13640609929636263757783763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36374959812363370020756701 13640609929636263757783763)
          ·
            refine ⟨20460914894454395636675645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13640609929636263757783763 20460914894454395636675645)
            ·
              refine ⟨7672843085420398363753367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20460914894454395636675645 7672843085420398363753367)
              ·
                refine ⟨11509264628130597545630051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7672843085420398363753367 11509264628130597545630051)
                ·
                  refine ⟨17263896942195896318445077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11509264628130597545630051 17263896942195896318445077)
                  ·
                    refine ⟨809245169165432639927113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17263896942195896318445077 809245169165432639927113)
                    ·
                      rfl

theorem cell23_4727998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_4727998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4727998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4727998 prefixEnd_4727998 := by exact prefixLift 4727998
  have htrace : WordTrace (prefixWord ++ tailWord_4727998) baseStart_4727998 baseEnd_4727998 := by
    simpa [prefixWord, tailWord_4727998, baseEnd_4727998] using wordTrace_append hprefix tailTrace_4727998
  have hstable : (prefixWord ++ tailWord_4727998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4727998).length < 2 ^ (prefixWord ++ tailWord_4727998).sum := by decide
  have hdescent : baseEnd_4727998 < baseStart_4727998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4727998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728008 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_4728008 : Nat := 118140960795 + 4728008 * 2 ^ 59
def prefixEnd_4728008 : Nat := 4983230072969 + 3 ^ 40 * 4728008 * 2
def baseEnd_4728008 : Nat := 2427740642302842880656293

theorem tailTrace_4728008 : CollatzResearch.WordTrace tailWord_4728008 prefixEnd_4728008 2427740642302842880656293 := by
  unfold tailWord_4728008
  simp only [CollatzResearch.WordTrace]
  refine ⟨86222309327620985162392339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114963079103494646883189785 86222309327620985162392339)
  ·
    refine ⟨129333463991431477743588509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86222309327620985162392339 129333463991431477743588509)
    ·
      refine ⟨48500048996786804153845691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129333463991431477743588509 48500048996786804153845691)
      ·
        refine ⟨72750073495180206230768537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48500048996786804153845691 72750073495180206230768537)
        ·
          refine ⟨54562555121385154673076403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72750073495180206230768537 54562555121385154673076403)
          ·
            refine ⟨81843832682077732009614605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54562555121385154673076403 81843832682077732009614605)
            ·
              refine ⟨30691437255779149503605477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81843832682077732009614605 30691437255779149503605477)
              ·
                refine ⟨5754644485458590531926027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30691437255779149503605477 5754644485458590531926027)
                ·
                  refine ⟨8631966728187885797889041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5754644485458590531926027 8631966728187885797889041)
                  ·
                    refine ⟨6473975046140914348416781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8631966728187885797889041 6473975046140914348416781)
                    ·
                      refine ⟨2427740642302842880656293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6473975046140914348416781 2427740642302842880656293)
                      ·
                        rfl

theorem cell23_4728008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_4728008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728008 prefixEnd_4728008 := by exact prefixLift 4728008
  have htrace : WordTrace (prefixWord ++ tailWord_4728008) baseStart_4728008 baseEnd_4728008 := by
    simpa [prefixWord, tailWord_4728008, baseEnd_4728008] using wordTrace_append hprefix tailTrace_4728008
  have hstable : (prefixWord ++ tailWord_4728008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728008).length < 2 ^ (prefixWord ++ tailWord_4728008).sum := by decide
  have hdescent : baseEnd_4728008 < baseStart_4728008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728039 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4728039 : Nat := 118140960795 + 4728039 * 2 ^ 59
def prefixEnd_4728039 : Nat := 4983230072969 + 3 ^ 40 * 4728039 * 2
def baseEnd_4728039 : Nat := 2427756560203132259368651

theorem tailTrace_4728039 : CollatzResearch.WordTrace tailWord_4728039 prefixEnd_4728039 2427756560203132259368651 := by
  unfold tailWord_4728039
  simp only [CollatzResearch.WordTrace]
  refine ⟨172445749318129662619163171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114963832878753108412775447 172445749318129662619163171)
  ·
    refine ⟨258668623977194493928744757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172445749318129662619163171 258668623977194493928744757)
    ·
      refine ⟨24250183497861983805819821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 258668623977194493928744757 24250183497861983805819821)
      ·
        refine ⟨9093818811698243927182433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24250183497861983805819821 9093818811698243927182433)
        ·
          refine ⟨6820364108773682945386825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9093818811698243927182433 6820364108773682945386825)
          ·
            refine ⟨5115273081580262209040119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6820364108773682945386825 5115273081580262209040119)
            ·
              refine ⟨7672909622370393313560179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5115273081580262209040119 7672909622370393313560179)
              ·
                refine ⟨11509364433555589970340269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7672909622370393313560179 11509364433555589970340269)
                ·
                  refine ⟨4316011662583346238877601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11509364433555589970340269 4316011662583346238877601)
                  ·
                    refine ⟨3237008746937509679158201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4316011662583346238877601 3237008746937509679158201)
                    ·
                      refine ⟨2427756560203132259368651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237008746937509679158201 2427756560203132259368651)
                      ·
                        rfl

theorem cell23_4728039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4728039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728039 prefixEnd_4728039 := by exact prefixLift 4728039
  have htrace : WordTrace (prefixWord ++ tailWord_4728039) baseStart_4728039 baseEnd_4728039 := by
    simpa [prefixWord, tailWord_4728039, baseEnd_4728039] using wordTrace_append hprefix tailTrace_4728039
  have hstable : (prefixWord ++ tailWord_4728039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728039).length < 2 ^ (prefixWord ++ tailWord_4728039).sum := by decide
  have hdescent : baseEnd_4728039 < baseStart_4728039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728065 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_4728065 : Nat := 118140960795 + 4728065 * 2 ^ 59
def prefixEnd_4728065 : Nat := 4983230072969 + 3 ^ 40 * 4728065 * 2
def baseEnd_4728065 : Nat := 2427769910700149157643531

theorem tailTrace_4728065 : CollatzResearch.WordTrace tailWord_4728065 prefixEnd_4728065 2427769910700149157643531 := by
  unfold tailWord_4728065
  simp only [CollatzResearch.WordTrace]
  refine ⟨172446697616035469059609649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114964465077356979373073099 172446697616035469059609649)
  ·
    refine ⟨129335023212026601794707237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172446697616035469059609649 129335023212026601794707237)
    ·
      refine ⟨24250316852254987836507607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129335023212026601794707237 24250316852254987836507607)
      ·
        refine ⟨36375475278382481754761411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24250316852254987836507607 36375475278382481754761411)
        ·
          refine ⟨54563212917573722632142117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36375475278382481754761411 54563212917573722632142117)
          ·
            refine ⟨10230602422045072993526647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54563212917573722632142117 10230602422045072993526647)
            ·
              refine ⟨15345903633067609490289971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10230602422045072993526647 15345903633067609490289971)
              ·
                refine ⟨23018855449601414235434957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15345903633067609490289971 23018855449601414235434957)
                ·
                  refine ⟨8632070793600530338288109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23018855449601414235434957 8632070793600530338288109)
                  ·
                    refine ⟨3237026547600198876858041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8632070793600530338288109 3237026547600198876858041)
                    ·
                      refine ⟨2427769910700149157643531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237026547600198876858041 2427769910700149157643531)
                      ·
                        rfl

theorem cell23_4728065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_4728065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728065 prefixEnd_4728065 := by exact prefixLift 4728065
  have htrace : WordTrace (prefixWord ++ tailWord_4728065) baseStart_4728065 baseEnd_4728065 := by
    simpa [prefixWord, tailWord_4728065, baseEnd_4728065] using wordTrace_append hprefix tailTrace_4728065
  have hstable : (prefixWord ++ tailWord_4728065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728065).length < 2 ^ (prefixWord ++ tailWord_4728065).sum := by decide
  have hdescent : baseEnd_4728065 < baseStart_4728065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728081 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_4728081 : Nat := 118140960795 + 4728081 * 2 ^ 59
def prefixEnd_4728081 : Nat := 4983230072969 + 3 ^ 40 * 4728081 * 2
def baseEnd_4728081 : Nat := 2427778126390621095043457

theorem tailTrace_4728081 : CollatzResearch.WordTrace tailWord_4728081 prefixEnd_4728081 2427778126390621095043457 := by
  unfold tailWord_4728081
  simp only [CollatzResearch.WordTrace]
  refine ⟨172447281183977503792192097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114964854122651669194794731 172447281183977503792192097)
  ·
    refine ⟨129335460887983127844144073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172447281183977503792192097 129335460887983127844144073)
    ·
      refine ⟨97001595665987345883108055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129335460887983127844144073 97001595665987345883108055)
      ·
        refine ⟨145502393498981018824662083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97001595665987345883108055 145502393498981018824662083)
        ·
          refine ⟨218253590248471528236993125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145502393498981018824662083 218253590248471528236993125)
          ·
            refine ⟨40922548171588411544436211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218253590248471528236993125 40922548171588411544436211)
            ·
              refine ⟨61383822257382617316654317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40922548171588411544436211 61383822257382617316654317)
              ·
                refine ⟨23018933346518481493745369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61383822257382617316654317 23018933346518481493745369)
                ·
                  refine ⟨17264200009888861120309027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23018933346518481493745369 17264200009888861120309027)
                  ·
                    refine ⟨25896300014833291680463541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17264200009888861120309027 25896300014833291680463541)
                    ·
                      refine ⟨2427778126390621095043457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25896300014833291680463541 2427778126390621095043457)
                      ·
                        rfl

theorem cell23_4728081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_4728081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728081 prefixEnd_4728081 := by exact prefixLift 4728081
  have htrace : WordTrace (prefixWord ++ tailWord_4728081) baseStart_4728081 baseEnd_4728081 := by
    simpa [prefixWord, tailWord_4728081, baseEnd_4728081] using wordTrace_append hprefix tailTrace_4728081
  have hstable : (prefixWord ++ tailWord_4728081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728081).length < 2 ^ (prefixWord ++ tailWord_4728081).sum := by decide
  have hdescent : baseEnd_4728081 < baseStart_4728081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728091 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 4]
def baseStart_4728091 : Nat := 118140960795 + 4728091 * 2 ^ 59
def prefixEnd_4728091 : Nat := 4983230072969 + 3 ^ 40 * 4728091 * 2
def baseEnd_4728091 : Nat := 2427783261197166055918411

theorem tailTrace_4728091 : CollatzResearch.WordTrace tailWord_4728091 prefixEnd_4728091 2427783261197166055918411 := by
  unfold tailWord_4728091
  simp only [CollatzResearch.WordTrace]
  refine ⟨172447645913941275500056127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114965097275960850333370751 172447645913941275500056127)
  ·
    refine ⟨258671468870911913250084191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172447645913941275500056127 258671468870911913250084191)
    ·
      refine ⟨388007203306367869875126287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258671468870911913250084191 388007203306367869875126287)
      ·
        refine ⟨582010804959551804812689431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388007203306367869875126287 582010804959551804812689431)
        ·
          refine ⟨873016207439327707219034147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582010804959551804812689431 873016207439327707219034147)
          ·
            refine ⟨1309524311158991560828551221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873016207439327707219034147 1309524311158991560828551221)
            ·
              refine ⟨122767904171155458827676677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1309524311158991560828551221 122767904171155458827676677)
              ·
                refine ⟨23018982032091648530189377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122767904171155458827676677 23018982032091648530189377)
                ·
                  refine ⟨17264236524068736397642033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23018982032091648530189377 17264236524068736397642033)
                  ·
                    refine ⟨12948177393051552298231525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17264236524068736397642033 12948177393051552298231525)
                    ·
                      refine ⟨2427783261197166055918411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12948177393051552298231525 2427783261197166055918411)
                      ·
                        rfl

theorem cell23_4728091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 4].length) (baseStart_4728091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728091 prefixEnd_4728091 := by exact prefixLift 4728091
  have htrace : WordTrace (prefixWord ++ tailWord_4728091) baseStart_4728091 baseEnd_4728091 := by
    simpa [prefixWord, tailWord_4728091, baseEnd_4728091] using wordTrace_append hprefix tailTrace_4728091
  have hstable : (prefixWord ++ tailWord_4728091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728091).length < 2 ^ (prefixWord ++ tailWord_4728091).sum := by decide
  have hdescent : baseEnd_4728091 < baseStart_4728091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728135 : List Nat := [1, 1, 4, 1, 2, 4, 2, 3, 5]
def baseStart_4728135 : Nat := 118140960795 + 4728135 * 2 ^ 59
def prefixEnd_4728135 : Nat := 4983230072969 + 3 ^ 40 * 4728135 * 2
def baseEnd_4728135 : Nat := 269756206038440431529801

theorem tailTrace_4728135 : CollatzResearch.WordTrace tailWord_4728135 prefixEnd_4728135 269756206038440431529801 := by
  unfold tailWord_4728135
  simp only [CollatzResearch.WordTrace]
  refine ⟨172449250725781871014657859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114966167150521247343105239 172449250725781871014657859)
  ·
    refine ⟨258673876088672806521986789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172449250725781871014657859 258673876088672806521986789)
    ·
      refine ⟨48501351766626151222872523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258673876088672806521986789 48501351766626151222872523)
      ·
        refine ⟨72752027649939226834308785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48501351766626151222872523 72752027649939226834308785)
        ·
          refine ⟨54564020737454420125731589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72752027649939226834308785 54564020737454420125731589)
          ·
            refine ⟨10230753888272703773574673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54564020737454420125731589 10230753888272703773574673)
            ·
              refine ⟨7673065416204527830181005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10230753888272703773574673 7673065416204527830181005)
              ·
                refine ⟨2877399531076697936317877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7673065416204527830181005 2877399531076697936317877)
                ·
                  refine ⟨269756206038440431529801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2877399531076697936317877 269756206038440431529801)
                  ·
                    rfl

theorem cell23_4728135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 5].length) (baseStart_4728135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728135 prefixEnd_4728135 := by exact prefixLift 4728135
  have htrace : WordTrace (prefixWord ++ tailWord_4728135) baseStart_4728135 baseEnd_4728135 := by
    simpa [prefixWord, tailWord_4728135, baseEnd_4728135] using wordTrace_append hprefix tailTrace_4728135
  have hstable : (prefixWord ++ tailWord_4728135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728135).length < 2 ^ (prefixWord ++ tailWord_4728135).sum := by decide
  have hdescent : baseEnd_4728135 < baseStart_4728135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728148 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_4728148 : Nat := 118140960795 + 4728148 * 2 ^ 59
def prefixEnd_4728148 : Nat := 4983230072969 + 3 ^ 40 * 4728148 * 2
def baseEnd_4728148 : Nat := 809270843198157444301883

theorem tailTrace_4728148 : CollatzResearch.WordTrace tailWord_4728148 prefixEnd_4728148 809270843198157444301883 := by
  unfold tailWord_4728148
  simp only [CollatzResearch.WordTrace]
  refine ⟨86224862437367387117440549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114966483249823182823254065 86224862437367387117440549)
  ·
    refine ⟨16167161707006385084520103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86224862437367387117440549 16167161707006385084520103)
    ·
      refine ⟨24250742560509577626780155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16167161707006385084520103 24250742560509577626780155)
      ·
        refine ⟨36376113840764366440170233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24250742560509577626780155 36376113840764366440170233)
        ·
          refine ⟨27282085380573274830127675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36376113840764366440170233 27282085380573274830127675)
          ·
            refine ⟨40923128070859912245191513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27282085380573274830127675 40923128070859912245191513)
            ·
              refine ⟨30692346053144934183893635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40923128070859912245191513 30692346053144934183893635)
              ·
                refine ⟨46038519079717401275840453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30692346053144934183893635 46038519079717401275840453)
                ·
                  refine ⟨8632222327447012739220085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46038519079717401275840453 8632222327447012739220085)
                  ·
                    refine ⟨809270843198157444301883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8632222327447012739220085 809270843198157444301883)
                    ·
                      rfl

theorem cell23_4728148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_4728148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728148 prefixEnd_4728148 := by exact prefixLift 4728148
  have htrace : WordTrace (prefixWord ++ tailWord_4728148) baseStart_4728148 baseEnd_4728148 := by
    simpa [prefixWord, tailWord_4728148, baseEnd_4728148] using wordTrace_append hprefix tailTrace_4728148
  have hstable : (prefixWord ++ tailWord_4728148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728148).length < 2 ^ (prefixWord ++ tailWord_4728148).sum := by decide
  have hdescent : baseEnd_4728148 < baseStart_4728148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728188 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 1, 4, 3]
def baseStart_4728188 : Nat := 118140960795 + 4728188 * 2 ^ 59
def prefixEnd_4728188 : Nat := 4983230072969 + 3 ^ 40 * 4728188 * 2
def baseEnd_4728188 : Nat := 2427833068820652176405465

theorem tailTrace_4728188 : CollatzResearch.WordTrace tailWord_4728188 prefixEnd_4728188 2427833068820652176405465 := by
  unfold tailWord_4728188
  simp only [CollatzResearch.WordTrace]
  refine ⟨86225591897294930533168609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114967455863059907377558145 86225591897294930533168609)
  ·
    refine ⟨64669193922971197899876457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86225591897294930533168609 64669193922971197899876457)
    ·
      refine ⟨48501895442228398424907343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64669193922971197899876457 48501895442228398424907343)
      ·
        refine ⟨72752843163342597637361015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48501895442228398424907343 72752843163342597637361015)
        ·
          refine ⟨109129264745013896456041523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72752843163342597637361015 109129264745013896456041523)
          ·
            refine ⟨163693897117520844684062285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109129264745013896456041523 163693897117520844684062285)
            ·
              refine ⟨61385211419070316756523357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163693897117520844684062285 61385211419070316756523357)
              ·
                refine ⟨23019454282151368783696259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61385211419070316756523357 23019454282151368783696259)
                ·
                  refine ⟨34529181423227053175544389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23019454282151368783696259 34529181423227053175544389)
                  ·
                    refine ⟨6474221516855072470414573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34529181423227053175544389 6474221516855072470414573)
                    ·
                      refine ⟨2427833068820652176405465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6474221516855072470414573 2427833068820652176405465)
                      ·
                        rfl

theorem cell23_4728188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_4728188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728188 prefixEnd_4728188 := by exact prefixLift 4728188
  have htrace : WordTrace (prefixWord ++ tailWord_4728188) baseStart_4728188 baseEnd_4728188 := by
    simpa [prefixWord, tailWord_4728188, baseEnd_4728188] using wordTrace_append hprefix tailTrace_4728188
  have hstable : (prefixWord ++ tailWord_4728188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728188).length < 2 ^ (prefixWord ++ tailWord_4728188).sum := by decide
  have hdescent : baseEnd_4728188 < baseStart_4728188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728212 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_4728212 : Nat := 118140960795 + 4728212 * 2 ^ 59
def prefixEnd_4728212 : Nat := 4983230072969 + 3 ^ 40 * 4728212 * 2
def baseEnd_4728212 : Nat := 809281797452120027501785

theorem tailTrace_4728212 : CollatzResearch.WordTrace tailWord_4728212 prefixEnd_4728212 809281797452120027501785 := by
  unfold tailWord_4728212
  simp only [CollatzResearch.WordTrace]
  refine ⟨86226029573251456582605445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114968039431001942110140593 86226029573251456582605445)
  ·
    refine ⟨16167380544984648109238521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86226029573251456582605445 16167380544984648109238521)
    ·
      refine ⟨12125535408738486081928891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16167380544984648109238521 12125535408738486081928891)
      ·
        refine ⟨18188303113107729122893337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12125535408738486081928891 18188303113107729122893337)
        ·
          refine ⟨13641227334830796842170003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18188303113107729122893337 13641227334830796842170003)
          ·
            refine ⟨20461841002246195263255005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13641227334830796842170003 20461841002246195263255005)
            ·
              refine ⟨7673190375842323223720627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20461841002246195263255005 7673190375842323223720627)
              ·
                refine ⟨11509785563763484835580941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7673190375842323223720627 11509785563763484835580941)
                ·
                  refine ⟨4316169586411306813342853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11509785563763484835580941 4316169586411306813342853)
                  ·
                    refine ⟨809281797452120027501785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4316169586411306813342853 809281797452120027501785)
                    ·
                      rfl

theorem cell23_4728212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_4728212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728212 prefixEnd_4728212 := by exact prefixLift 4728212
  have htrace : WordTrace (prefixWord ++ tailWord_4728212) baseStart_4728212 baseEnd_4728212 := by
    simpa [prefixWord, tailWord_4728212, baseEnd_4728212] using wordTrace_append hprefix tailTrace_4728212
  have hstable : (prefixWord ++ tailWord_4728212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728212).length < 2 ^ (prefixWord ++ tailWord_4728212).sum := by decide
  have hdescent : baseEnd_4728212 < baseStart_4728212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728285 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4728285 : Nat := 118140960795 + 4728285 * 2 ^ 59
def prefixEnd_4728285 : Nat := 4983230072969 + 3 ^ 40 * 4728285 * 2
def baseEnd_4728285 : Nat := 809294292148046098964173

theorem tailTrace_4728285 : CollatzResearch.WordTrace tailWord_4728285 prefixEnd_4728285 809294292148046098964173 := by
  unfold tailWord_4728285
  simp only [CollatzResearch.WordTrace]
  refine ⟨172454721675238446632618309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114969814450158964421745539 172454721675238446632618309)
  ·
    refine ⟨32335260314107208743615933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172454721675238446632618309 32335260314107208743615933)
    ·
      refine ⟨12125722617790203278855975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32335260314107208743615933 12125722617790203278855975)
      ·
        refine ⟨18188583926685304918283963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12125722617790203278855975 18188583926685304918283963)
        ·
          refine ⟨27282875890027957377425945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18188583926685304918283963 27282875890027957377425945)
          ·
            refine ⟨20462156917520968033069459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27282875890027957377425945 20462156917520968033069459)
            ·
              refine ⟨30693235376281452049604189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20462156917520968033069459 30693235376281452049604189)
              ·
                refine ⟨11509963266105544518601571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30693235376281452049604189 11509963266105544518601571)
                ·
                  refine ⟨17264944899158316777902357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11509963266105544518601571 17264944899158316777902357)
                  ·
                    refine ⟨809294292148046098964173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17264944899158316777902357 809294292148046098964173)
                    ·
                      rfl

theorem cell23_4728285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4728285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728285 prefixEnd_4728285 := by exact prefixLift 4728285
  have htrace : WordTrace (prefixWord ++ tailWord_4728285) baseStart_4728285 baseEnd_4728285 := by
    simpa [prefixWord, tailWord_4728285, baseEnd_4728285] using wordTrace_append hprefix tailTrace_4728285
  have hstable : (prefixWord ++ tailWord_4728285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728285).length < 2 ^ (prefixWord ++ tailWord_4728285).sum := by decide
  have hdescent : baseEnd_4728285 < baseStart_4728285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728305 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_4728305 : Nat := 118140960795 + 4728305 * 2 ^ 59
def prefixEnd_4728305 : Nat := 4983230072969 + 3 ^ 40 * 4728305 * 2
def baseEnd_4728305 : Nat := 2427893146057228218642427

theorem tailTrace_4728305 : CollatzResearch.WordTrace tailWord_4728305 prefixEnd_4728305 2427893146057228218642427 := by
  unfold tailWord_4728305
  simp only [CollatzResearch.WordTrace]
  refine ⟨172455451135165990048346369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114970300756777326698897579 172455451135165990048346369)
  ·
    refine ⟨129341588351374492536259777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172455451135165990048346369 129341588351374492536259777)
    ·
      refine ⟨97006191263530869402194833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129341588351374492536259777 97006191263530869402194833)
      ·
        refine ⟨72754643447648152051646125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97006191263530869402194833 72754643447648152051646125)
        ·
          refine ⟨27282991292868057019367297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72754643447648152051646125 27282991292868057019367297)
          ·
            refine ⟨20462243469651042764525473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27282991292868057019367297 20462243469651042764525473)
            ·
              refine ⟨15346682602238282073394105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20462243469651042764525473 15346682602238282073394105)
              ·
                refine ⟨11510011951678711555045579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15346682602238282073394105 11510011951678711555045579)
                ·
                  refine ⟨17265017927518067332568369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11510011951678711555045579 17265017927518067332568369)
                  ·
                    refine ⟨12948763445638550499426277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17265017927518067332568369 12948763445638550499426277)
                    ·
                      refine ⟨2427893146057228218642427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12948763445638550499426277 2427893146057228218642427)
                      ·
                        rfl

theorem cell23_4728305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_4728305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728305 prefixEnd_4728305 := by exact prefixLift 4728305
  have htrace : WordTrace (prefixWord ++ tailWord_4728305) baseStart_4728305 baseEnd_4728305 := by
    simpa [prefixWord, tailWord_4728305, baseEnd_4728305] using wordTrace_append hprefix tailTrace_4728305
  have hstable : (prefixWord ++ tailWord_4728305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728305).length < 2 ^ (prefixWord ++ tailWord_4728305).sum := by decide
  have hdescent : baseEnd_4728305 < baseStart_4728305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728309 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4728309 : Nat := 118140960795 + 4728309 * 2 ^ 59
def prefixEnd_4728309 : Nat := 4983230072969 + 3 ^ 40 * 4728309 * 2
def baseEnd_4728309 : Nat := 2427895199979846202992409

theorem tailTrace_4728309 : CollatzResearch.WordTrace tailWord_4728309 prefixEnd_4728309 2427895199979846202992409 := by
  unfold tailWord_4728309
  simp only [CollatzResearch.WordTrace]
  refine ⟨172455597027151498731491981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114970398018100999154327987 172455597027151498731491981)
  ·
    refine ⟨64670848885181812024309493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172455597027151498731491981 64670848885181812024309493)
    ·
      refine ⟨6062892082985794877279015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64670848885181812024309493 6062892082985794877279015)
      ·
        refine ⟨9094338124478692315918523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6062892082985794877279015 9094338124478692315918523)
        ·
          refine ⟨13641507186718038473877785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9094338124478692315918523 13641507186718038473877785)
          ·
            refine ⟨10231130390038528855408339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13641507186718038473877785 10231130390038528855408339)
            ·
              refine ⟨15346695585057793283112509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10231130390038528855408339 15346695585057793283112509)
              ·
                refine ⟨5755010844396672481167191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15346695585057793283112509 5755010844396672481167191)
                ·
                  refine ⟨8632516266595008721750787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5755010844396672481167191 8632516266595008721750787)
                  ·
                    refine ⟨12948774399892513082626181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8632516266595008721750787 12948774399892513082626181)
                    ·
                      refine ⟨2427895199979846202992409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12948774399892513082626181 2427895199979846202992409)
                      ·
                        rfl

theorem cell23_4728309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4728309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728309 prefixEnd_4728309 := by exact prefixLift 4728309
  have htrace : WordTrace (prefixWord ++ tailWord_4728309) baseStart_4728309 baseEnd_4728309 := by
    simpa [prefixWord, tailWord_4728309, baseEnd_4728309] using wordTrace_append hprefix tailTrace_4728309
  have hstable : (prefixWord ++ tailWord_4728309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728309).length < 2 ^ (prefixWord ++ tailWord_4728309).sum := by decide
  have hdescent : baseEnd_4728309 < baseStart_4728309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728312 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 1, 2, 3]
def baseStart_4728312 : Nat := 118140960795 + 4728312 * 2 ^ 59
def prefixEnd_4728312 : Nat := 4983230072969 + 3 ^ 40 * 4728312 * 2
def baseEnd_4728312 : Nat := 2427896740421809691254895

theorem tailTrace_4728312 : CollatzResearch.WordTrace tailWord_4728312 prefixEnd_4728312 2427896740421809691254895 := by
  unfold tailWord_4728312
  simp only [CollatzResearch.WordTrace]
  refine ⟨86227853223070315121925595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114970470964093753495900793 86227853223070315121925595)
  ·
    refine ⟨129341779834605472682888393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86227853223070315121925595 129341779834605472682888393)
    ·
      refine ⟨97006334875954104512166295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129341779834605472682888393 97006334875954104512166295)
      ·
        refine ⟨145509502313931156768249443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97006334875954104512166295 145509502313931156768249443)
        ·
          refine ⟨218264253470896735152374165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145509502313931156768249443 218264253470896735152374165)
          ·
            refine ⟨10231136881448284460267539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 218264253470896735152374165 10231136881448284460267539)
            ·
              refine ⟨15346705322172426690401309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10231136881448284460267539 15346705322172426690401309)
              ·
                refine ⟨5755014495814660008900491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15346705322172426690401309 5755014495814660008900491)
                ·
                  refine ⟨8632521743721990013350737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5755014495814660008900491 8632521743721990013350737)
                  ·
                    refine ⟨6474391307791492510013053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8632521743721990013350737 6474391307791492510013053)
                    ·
                      refine ⟨2427896740421809691254895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6474391307791492510013053 2427896740421809691254895)
                      ·
                        rfl

theorem cell23_4728312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_4728312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728312 prefixEnd_4728312 := by exact prefixLift 4728312
  have htrace : WordTrace (prefixWord ++ tailWord_4728312) baseStart_4728312 baseEnd_4728312 := by
    simpa [prefixWord, tailWord_4728312, baseEnd_4728312] using wordTrace_append hprefix tailTrace_4728312
  have hstable : (prefixWord ++ tailWord_4728312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728312).length < 2 ^ (prefixWord ++ tailWord_4728312).sum := by decide
  have hdescent : baseEnd_4728312 < baseStart_4728312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728328 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 1, 9]
def baseStart_4728328 : Nat := 118140960795 + 4728328 * 2 ^ 59
def prefixEnd_4728328 : Nat := 4983230072969 + 3 ^ 40 * 4728328 * 2
def baseEnd_4728328 : Nat := 809301652037427209551607

theorem tailTrace_4728328 : CollatzResearch.WordTrace tailWord_4728328 prefixEnd_4728328 809301652037427209551607 := by
  unfold tailWord_4728328
  simp only [CollatzResearch.WordTrace]
  refine ⟨86228145007041332488216819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114970860009388443317622425 86228145007041332488216819)
  ·
    refine ⟨129342217510561998732325229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86228145007041332488216819 129342217510561998732325229)
    ·
      refine ⟨48503331566460749524621961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129342217510561998732325229 48503331566460749524621961)
      ·
        refine ⟨36377498674845562143466471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48503331566460749524621961 36377498674845562143466471)
        ·
          refine ⟨54566248012268343215199707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36377498674845562143466471 54566248012268343215199707)
          ·
            refine ⟨81849372018402514822799561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54566248012268343215199707 81849372018402514822799561)
            ·
              refine ⟨61387029013801886117099671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81849372018402514822799561 61387029013801886117099671)
              ·
                refine ⟨92080543520702829175649507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61387029013801886117099671 92080543520702829175649507)
                ·
                  refine ⟨138120815281054243763474261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92080543520702829175649507 138120815281054243763474261)
                  ·
                    refine ⟨809301652037427209551607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138120815281054243763474261 809301652037427209551607)
                    ·
                      rfl

theorem cell23_4728328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_4728328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728328 prefixEnd_4728328 := by exact prefixLift 4728328
  have htrace : WordTrace (prefixWord ++ tailWord_4728328) baseStart_4728328 baseEnd_4728328 := by
    simpa [prefixWord, tailWord_4728328, baseEnd_4728328] using wordTrace_append hprefix tailTrace_4728328
  have hstable : (prefixWord ++ tailWord_4728328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728328).length < 2 ^ (prefixWord ++ tailWord_4728328).sum := by decide
  have hdescent : baseEnd_4728328 < baseStart_4728328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728360 : List Nat := [2, 1, 5, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4728360 : Nat := 118140960795 + 4728360 * 2 ^ 59
def prefixEnd_4728360 : Nat := 4983230072969 + 3 ^ 40 * 4728360 * 2
def baseEnd_4728360 : Nat := 2427921387493225503454675

theorem tailTrace_4728360 : CollatzResearch.WordTrace tailWord_4728360 prefixEnd_4728360 2427921387493225503454675 := by
  unfold tailWord_4728360
  simp only [CollatzResearch.WordTrace]
  refine ⟨86228728574983367220799267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114971638099977822961065689 86228728574983367220799267)
  ·
    refine ⟨129343092862475050831198901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86228728574983367220799267 129343092862475050831198901)
    ·
      refine ⟨12125914955857036015424897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129343092862475050831198901 12125914955857036015424897)
      ·
        refine ⟨9094436216892777011568673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12125914955857036015424897 9094436216892777011568673)
        ·
          refine ⟨6820827162669582758676505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9094436216892777011568673 6820827162669582758676505)
          ·
            refine ⟨5115620372002187069007379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6820827162669582758676505 5115620372002187069007379)
            ·
              refine ⟨7673430558003280603511069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5115620372002187069007379 7673430558003280603511069)
              ·
                refine ⟨2877536459251230226316651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7673430558003280603511069 2877536459251230226316651)
                ·
                  refine ⟨4316304688876845339474977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877536459251230226316651 4316304688876845339474977)
                  ·
                    refine ⟨3237228516657634004606233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4316304688876845339474977 3237228516657634004606233)
                    ·
                      refine ⟨2427921387493225503454675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237228516657634004606233 2427921387493225503454675)
                      ·
                        rfl

theorem cell23_4728360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4728360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728360 prefixEnd_4728360 := by exact prefixLift 4728360
  have htrace : WordTrace (prefixWord ++ tailWord_4728360) baseStart_4728360 baseEnd_4728360 := by
    simpa [prefixWord, tailWord_4728360, baseEnd_4728360] using wordTrace_append hprefix tailTrace_4728360
  have hstable : (prefixWord ++ tailWord_4728360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728360).length < 2 ^ (prefixWord ++ tailWord_4728360).sum := by decide
  have hdescent : baseEnd_4728360 < baseStart_4728360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728385 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_4728385 : Nat := 118140960795 + 4728385 * 2 ^ 59
def prefixEnd_4728385 : Nat := 4983230072969 + 3 ^ 40 * 4728385 * 2
def baseEnd_4728385 : Nat := 2427934224509587905642059

theorem tailTrace_4728385 : CollatzResearch.WordTrace tailWord_4728385 prefixEnd_4728385 2427934224509587905642059 := by
  unfold tailWord_4728385
  simp only [CollatzResearch.WordTrace]
  refine ⟨172458368974876163711258609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114972245983250775807505739 172458368974876163711258609)
  ·
    refine ⟨129343776731157122783443957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172458368974876163711258609 129343776731157122783443957)
    ·
      refine ⟨12125979068545980260947871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129343776731157122783443957 12125979068545980260947871)
      ·
        refine ⟨18188968602818970391421807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12125979068545980260947871 18188968602818970391421807)
        ·
          refine ⟨27283452904228455587132711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18188968602818970391421807 27283452904228455587132711)
          ·
            refine ⟨40925179356342683380699067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27283452904228455587132711 40925179356342683380699067)
            ·
              refine ⟨61387769034514025071048601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40925179356342683380699067 61387769034514025071048601)
              ·
                refine ⟨46040826775885518803286451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61387769034514025071048601 46040826775885518803286451)
                ·
                  refine ⟨69061240163828278204929677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46040826775885518803286451 69061240163828278204929677)
                  ·
                    refine ⟨25897965061435604326848629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69061240163828278204929677 25897965061435604326848629)
                    ·
                      refine ⟨2427934224509587905642059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25897965061435604326848629 2427934224509587905642059)
                      ·
                        rfl

theorem cell23_4728385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_4728385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728385 prefixEnd_4728385 := by exact prefixLift 4728385
  have htrace : WordTrace (prefixWord ++ tailWord_4728385) baseStart_4728385 baseEnd_4728385 := by
    simpa [prefixWord, tailWord_4728385, baseEnd_4728385] using wordTrace_append hprefix tailTrace_4728385
  have hstable : (prefixWord ++ tailWord_4728385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728385).length < 2 ^ (prefixWord ++ tailWord_4728385).sum := by decide
  have hdescent : baseEnd_4728385 < baseStart_4728385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728415 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 3]
def baseStart_4728415 : Nat := 118140960795 + 4728415 * 2 ^ 59
def prefixEnd_4728415 : Nat := 4983230072969 + 3 ^ 40 * 4728415 * 2
def baseEnd_4728415 : Nat := 2427949628929222788266921

theorem tailTrace_4728415 : CollatzResearch.WordTrace tailWord_4728415 prefixEnd_4728415 2427949628929222788266921 := by
  unfold tailWord_4728415
  simp only [CollatzResearch.WordTrace]
  refine ⟨172459463164767478834850699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114972975443178319223233799 172459463164767478834850699)
  ·
    refine ⟨258689194747151218252276049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172459463164767478834850699 258689194747151218252276049)
    ·
      refine ⟨194016896060363413689207037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258689194747151218252276049 194016896060363413689207037)
      ·
        refine ⟨72756336022636280133452639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194016896060363413689207037 72756336022636280133452639)
        ·
          refine ⟨109134504033954420200178959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72756336022636280133452639 109134504033954420200178959)
          ·
            refine ⟨163701756050931630300268439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109134504033954420200178959 163701756050931630300268439)
            ·
              refine ⟨245552634076397445450402659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163701756050931630300268439 245552634076397445450402659)
              ·
                refine ⟨368328951114596168175603989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245552634076397445450402659 368328951114596168175603989)
                ·
                  refine ⟨17265419583496695383231437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 368328951114596168175603989 17265419583496695383231437)
                  ·
                    refine ⟨6474532343811260768711789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17265419583496695383231437 6474532343811260768711789)
                    ·
                      refine ⟨2427949628929222788266921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6474532343811260768711789 2427949628929222788266921)
                      ·
                        rfl

theorem cell23_4728415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_4728415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728415 prefixEnd_4728415 := by exact prefixLift 4728415
  have htrace : WordTrace (prefixWord ++ tailWord_4728415) baseStart_4728415 baseEnd_4728415 := by
    simpa [prefixWord, tailWord_4728415, baseEnd_4728415] using wordTrace_append hprefix tailTrace_4728415
  have hstable : (prefixWord ++ tailWord_4728415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728415).length < 2 ^ (prefixWord ++ tailWord_4728415).sum := by decide
  have hdescent : baseEnd_4728415 < baseStart_4728415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728472 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4728472 : Nat := 118140960795 + 4728472 * 2 ^ 59
def prefixEnd_4728472 : Nat := 4983230072969 + 3 ^ 40 * 4728472 * 2
def baseEnd_4728472 : Nat := 2427978897326529065254159

theorem tailTrace_4728472 : CollatzResearch.WordTrace tailWord_4728472 prefixEnd_4728472 2427978897326529065254159 := by
  unfold tailWord_4728472
  simp only [CollatzResearch.WordTrace]
  refine ⟨86230771062780488784837835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114974361417040651713117113 86230771062780488784837835)
  ·
    refine ⟨129346156594170733177256753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86230771062780488784837835 129346156594170733177256753)
    ·
      refine ⟨97009617445628049882942565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129346156594170733177256753 97009617445628049882942565)
      ·
        refine ⟨18189303271055259353051731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97009617445628049882942565 18189303271055259353051731)
        ·
          refine ⟨27283954906582889029577597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18189303271055259353051731 27283954906582889029577597)
          ·
            refine ⟨10231483089968583386091599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27283954906582889029577597 10231483089968583386091599)
            ·
              refine ⟨15347224634952875079137399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10231483089968583386091599 15347224634952875079137399)
              ·
                refine ⟨23020836952429312618706099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15347224634952875079137399 23020836952429312618706099)
                ·
                  refine ⟨34531255428643968928059149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23020836952429312618706099 34531255428643968928059149)
                  ·
                    refine ⟨12949220785741488348022181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34531255428643968928059149 12949220785741488348022181)
                    ·
                      refine ⟨2427978897326529065254159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12949220785741488348022181 2427978897326529065254159)
                      ·
                        rfl

theorem cell23_4728472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4728472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728472 prefixEnd_4728472 := by exact prefixLift 4728472
  have htrace : WordTrace (prefixWord ++ tailWord_4728472) baseStart_4728472 baseEnd_4728472 := by
    simpa [prefixWord, tailWord_4728472, baseEnd_4728472] using wordTrace_append hprefix tailTrace_4728472
  have hstable : (prefixWord ++ tailWord_4728472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728472).length < 2 ^ (prefixWord ++ tailWord_4728472).sum := by decide
  have hdescent : baseEnd_4728472 < baseStart_4728472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728485 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_4728485 : Nat := 118140960795 + 4728485 * 2 ^ 59
def prefixEnd_4728485 : Nat := 4983230072969 + 3 ^ 40 * 4728485 * 2
def baseEnd_4728485 : Nat := 2427985572575037514391599

theorem tailTrace_4728485 : CollatzResearch.WordTrace tailWord_4728485 prefixEnd_4728485 2427985572575037514391599 := by
  unfold tailWord_4728485
  simp only [CollatzResearch.WordTrace]
  refine ⟨172462016274513880789898909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114974677516342587193265939 172462016274513880789898909)
  ·
    refine ⟨64673256102942705296212091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172462016274513880789898909 64673256102942705296212091)
    ·
      refine ⟨97009884154414057944318137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64673256102942705296212091 97009884154414057944318137)
      ·
        refine ⟨72757413115810543458238603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97009884154414057944318137 72757413115810543458238603)
        ·
          refine ⟨109136119673715815187357905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72757413115810543458238603 109136119673715815187357905)
          ·
            refine ⟨81852089755286861390518429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109136119673715815187357905 81852089755286861390518429)
            ·
              refine ⟨30694533658232573021444411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81852089755286861390518429 30694533658232573021444411)
              ·
                refine ⟨46041800487348859532166617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30694533658232573021444411 46041800487348859532166617)
                ·
                  refine ⟨34531350365511644649124963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46041800487348859532166617 34531350365511644649124963)
                  ·
                    refine ⟨51797025548267466973687445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34531350365511644649124963 51797025548267466973687445)
                    ·
                      refine ⟨2427985572575037514391599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51797025548267466973687445 2427985572575037514391599)
                      ·
                        rfl

theorem cell23_4728485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_4728485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728485 prefixEnd_4728485 := by exact prefixLift 4728485
  have htrace : WordTrace (prefixWord ++ tailWord_4728485) baseStart_4728485 baseEnd_4728485 := by
    simpa [prefixWord, tailWord_4728485, baseEnd_4728485] using wordTrace_append hprefix tailTrace_4728485
  have hstable : (prefixWord ++ tailWord_4728485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728485).length < 2 ^ (prefixWord ++ tailWord_4728485).sum := by decide
  have hdescent : baseEnd_4728485 < baseStart_4728485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728495 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 8]
def baseStart_4728495 : Nat := 118140960795 + 4728495 * 2 ^ 59
def prefixEnd_4728495 : Nat := 4983230072969 + 3 ^ 40 * 4728495 * 2
def baseEnd_4728495 : Nat := 269776745264620275029617

theorem tailTrace_4728495 : CollatzResearch.WordTrace tailWord_4728495 prefixEnd_4728495 269776745264620275029617 := by
  unfold tailWord_4728495
  simp only [CollatzResearch.WordTrace]
  refine ⟨172462381004477652497762939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114974920669651768331841959 172462381004477652497762939)
  ·
    refine ⟨258693571506716478746644409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172462381004477652497762939 258693571506716478746644409)
    ·
      refine ⟨194020178630037359059983307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258693571506716478746644409 194020178630037359059983307)
      ·
        refine ⟨291030267945056038589974961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194020178630037359059983307 291030267945056038589974961)
        ·
          refine ⟨218272700958792028942481221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291030267945056038589974961 218272700958792028942481221)
          ·
            refine ⟨40926131429773505426715229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218272700958792028942481221 40926131429773505426715229)
            ·
              refine ⟨15347299286165064535018211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40926131429773505426715229 15347299286165064535018211)
              ·
                refine ⟨23020948929247596802527317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15347299286165064535018211 23020948929247596802527317)
                ·
                  refine ⟨269776745264620275029617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23020948929247596802527317 269776745264620275029617)
                  ·
                    rfl

theorem cell23_4728495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 8].length) (baseStart_4728495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728495 prefixEnd_4728495 := by exact prefixLift 4728495
  have htrace : WordTrace (prefixWord ++ tailWord_4728495) baseStart_4728495 baseEnd_4728495 := by
    simpa [prefixWord, tailWord_4728495, baseEnd_4728495] using wordTrace_append hprefix tailTrace_4728495
  have hstable : (prefixWord ++ tailWord_4728495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728495).length < 2 ^ (prefixWord ++ tailWord_4728495).sum := by decide
  have hdescent : baseEnd_4728495 < baseStart_4728495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728499 : List Nat := [1, 1, 1, 2, 3, 3, 1, 6, 1, 4]
def baseStart_4728499 : Nat := 118140960795 + 4728499 * 2 ^ 59
def prefixEnd_4728499 : Nat := 4983230072969 + 3 ^ 40 * 4728499 * 2
def baseEnd_4728499 : Nat := 809330920434733486538845

theorem tailTrace_4728499 : CollatzResearch.WordTrace tailWord_4728499 prefixEnd_4728499 809330920434733486538845 := by
  unfold tailWord_4728499
  simp only [CollatzResearch.WordTrace]
  refine ⟨172462526896463161180908551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114975017930975440787272367 172462526896463161180908551)
  ·
    refine ⟨258693790344694741771362827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172462526896463161180908551 258693790344694741771362827)
    ·
      refine ⟨388040685517042112657044241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258693790344694741771362827 388040685517042112657044241)
      ·
        refine ⟨291030514137781584492783181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388040685517042112657044241 291030514137781584492783181)
        ·
          refine ⟨109136442801668094184793693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291030514137781584492783181 109136442801668094184793693)
          ·
            refine ⟨40926166050625535319297635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109136442801668094184793693 40926166050625535319297635)
            ·
              refine ⟨61389249075938302978946453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40926166050625535319297635 61389249075938302978946453)
              ·
                refine ⟨2877621050434607952138115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61389249075938302978946453 2877621050434607952138115)
                ·
                  refine ⟨4316431575651911928207173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877621050434607952138115 4316431575651911928207173)
                  ·
                    refine ⟨809330920434733486538845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4316431575651911928207173 809330920434733486538845)
                    ·
                      rfl

theorem cell23_4728499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 1, 4].length) (baseStart_4728499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728499 prefixEnd_4728499 := by exact prefixLift 4728499
  have htrace : WordTrace (prefixWord ++ tailWord_4728499) baseStart_4728499 baseEnd_4728499 := by
    simpa [prefixWord, tailWord_4728499, baseEnd_4728499] using wordTrace_append hprefix tailTrace_4728499
  have hstable : (prefixWord ++ tailWord_4728499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728499).length < 2 ^ (prefixWord ++ tailWord_4728499).sum := by decide
  have hdescent : baseEnd_4728499 < baseStart_4728499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728556 : List Nat := [2, 2, 1, 1, 2, 2, 2, 6, 1, 1, 3]
def baseStart_4728556 : Nat := 118140960795 + 4728556 * 2 ^ 59
def prefixEnd_4728556 : Nat := 4983230072969 + 3 ^ 40 * 4728556 * 2
def baseEnd_4728556 : Nat := 2428022029701506736603773

theorem tailTrace_4728556 : CollatzResearch.WordTrace tailWord_4728556 prefixEnd_4728556 2428022029701506736603773 := by
  unfold tailWord_4728556
  simp only [CollatzResearch.WordTrace]
  refine ⟨86232302928628329957866761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114976403904837773277155681 86232302928628329957866761)
  ·
    refine ⟨64674227196471247468400071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86232302928628329957866761 64674227196471247468400071)
    ·
      refine ⟨97011340794706871202600107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64674227196471247468400071 97011340794706871202600107)
      ·
        refine ⟨145517011192060306803900161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97011340794706871202600107 145517011192060306803900161)
        ·
          refine ⟨109137758394045230102925121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145517011192060306803900161 109137758394045230102925121)
          ·
            refine ⟨81853318795533922577193841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109137758394045230102925121 81853318795533922577193841)
            ·
              refine ⟨61389989096650441932895381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81853318795533922577193841 61389989096650441932895381)
              ·
                refine ⟨2877655738905489465604471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61389989096650441932895381 2877655738905489465604471)
                ·
                  refine ⟨4316483608358234198406707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877655738905489465604471 4316483608358234198406707)
                  ·
                    refine ⟨6474725412537351297610061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4316483608358234198406707 6474725412537351297610061)
                    ·
                      refine ⟨2428022029701506736603773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6474725412537351297610061 2428022029701506736603773)
                      ·
                        rfl

theorem cell23_4728556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 1, 3].length) (baseStart_4728556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728556 prefixEnd_4728556 := by exact prefixLift 4728556
  have htrace : WordTrace (prefixWord ++ tailWord_4728556) baseStart_4728556 baseEnd_4728556 := by
    simpa [prefixWord, tailWord_4728556, baseEnd_4728556] using wordTrace_append hprefix tailTrace_4728556
  have hstable : (prefixWord ++ tailWord_4728556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728556).length < 2 ^ (prefixWord ++ tailWord_4728556).sum := by decide
  have hdescent : baseEnd_4728556 < baseStart_4728556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728572 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_4728572 : Nat := 118140960795 + 4728572 * 2 ^ 59
def prefixEnd_4728572 : Nat := 4983230072969 + 3 ^ 40 * 4728572 * 2
def baseEnd_4728572 : Nat := 809343415130659558001233

theorem tailTrace_4728572 : CollatzResearch.WordTrace tailWord_4728572 prefixEnd_4728572 809343415130659558001233 := by
  unfold tailWord_4728572
  simp only [CollatzResearch.WordTrace]
  refine ⟨86232594712599347324157985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114976792950132463098877313 86232594712599347324157985)
  ·
    refine ⟨64674446034449510493118489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86232594712599347324157985 64674446034449510493118489)
    ·
      refine ⟨48505834525837132869838867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64674446034449510493118489 48505834525837132869838867)
      ·
        refine ⟨72758751788755699304758301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48505834525837132869838867 72758751788755699304758301)
        ·
          refine ⟨27284531920783387239284363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72758751788755699304758301 27284531920783387239284363)
          ·
            refine ⟨40926797881175080858926545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27284531920783387239284363 40926797881175080858926545)
            ·
              refine ⟨30695098410881310644194909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40926797881175080858926545 30695098410881310644194909)
              ·
                refine ⟨11510661904080491491573091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30695098410881310644194909 11510661904080491491573091)
                ·
                  refine ⟨17265992856120737237359637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11510661904080491491573091 17265992856120737237359637)
                  ·
                    refine ⟨809343415130659558001233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17265992856120737237359637 809343415130659558001233)
                    ·
                      rfl

theorem cell23_4728572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_4728572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728572 prefixEnd_4728572 := by exact prefixLift 4728572
  have htrace : WordTrace (prefixWord ++ tailWord_4728572) baseStart_4728572 baseEnd_4728572 := by
    simpa [prefixWord, tailWord_4728572, baseEnd_4728572] using wordTrace_append hprefix tailTrace_4728572
  have hstable : (prefixWord ++ tailWord_4728572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728572).length < 2 ^ (prefixWord ++ tailWord_4728572).sum := by decide
  have hdescent : baseEnd_4728572 < baseStart_4728572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728579 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 4]
def baseStart_4728579 : Nat := 118140960795 + 4728579 * 2 ^ 59
def prefixEnd_4728579 : Nat := 4983230072969 + 3 ^ 40 * 4728579 * 2
def baseEnd_4728579 : Nat := 2428033839756560146616167

theorem tailTrace_4728579 : CollatzResearch.WordTrace tailWord_4728579 prefixEnd_4728579 2428033839756560146616167 := by
  unfold tailWord_4728579
  simp only [CollatzResearch.WordTrace]
  refine ⟨172465444736173334843820791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114976963157448889895880527 172465444736173334843820791)
  ·
    refine ⟨258698167104260002265731187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172465444736173334843820791 258698167104260002265731187)
    ·
      refine ⟨388047250656390003398596781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258698167104260002265731187 388047250656390003398596781)
      ·
        refine ⟨145517718996146251274473793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 388047250656390003398596781 145517718996146251274473793)
        ·
          refine ⟨109138289247109688455855345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145517718996146251274473793 109138289247109688455855345)
          ·
            refine ⟨81853716935332266341891509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109138289247109688455855345 81853716935332266341891509)
            ·
              refine ⟨7673785962687399969552329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81853716935332266341891509 7673785962687399969552329)
              ·
                refine ⟨5755339472015549977164247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7673785962687399969552329 5755339472015549977164247)
                ·
                  refine ⟨8633009208023324965746371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5755339472015549977164247 8633009208023324965746371)
                  ·
                    refine ⟨12949513812034987448619557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8633009208023324965746371 12949513812034987448619557)
                    ·
                      refine ⟨2428033839756560146616167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12949513812034987448619557 2428033839756560146616167)
                      ·
                        rfl

theorem cell23_4728579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_4728579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728579 prefixEnd_4728579 := by exact prefixLift 4728579
  have htrace : WordTrace (prefixWord ++ tailWord_4728579) baseStart_4728579 baseEnd_4728579 := by
    simpa [prefixWord, tailWord_4728579, baseEnd_4728579] using wordTrace_append hprefix tailTrace_4728579
  have hstable : (prefixWord ++ tailWord_4728579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728579).length < 2 ^ (prefixWord ++ tailWord_4728579).sum := by decide
  have hdescent : baseEnd_4728579 < baseStart_4728579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728583 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4728583 : Nat := 118140960795 + 4728583 * 2 ^ 59
def prefixEnd_4728583 : Nat := 4983230072969 + 3 ^ 40 * 4728583 * 2
def baseEnd_4728583 : Nat := 2428035893679178130966149

theorem tailTrace_4728583 : CollatzResearch.WordTrace tailWord_4728583 prefixEnd_4728583 2428035893679178130966149 := by
  unfold tailWord_4728583
  simp only [CollatzResearch.WordTrace]
  refine ⟨172465590628158843526966403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114977060418772562351310935 172465590628158843526966403)
  ·
    refine ⟨258698385942238265290449605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172465590628158843526966403 258698385942238265290449605)
    ·
      refine ⟨48505947364169674741959301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258698385942238265290449605 48505947364169674741959301)
      ·
        refine ⟨9094865130781814014117369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48505947364169674741959301 9094865130781814014117369)
        ·
          refine ⟨6821148848086360510588027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9094865130781814014117369 6821148848086360510588027)
          ·
            refine ⟨10231723272129540765882041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6821148848086360510588027 10231723272129540765882041)
            ·
              refine ⟨7673792454097155574411531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10231723272129540765882041 7673792454097155574411531)
              ·
                refine ⟨11510688681145733361617297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7673792454097155574411531 11510688681145733361617297)
                ·
                  refine ⟨8633016510859300021212973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11510688681145733361617297 8633016510859300021212973)
                  ·
                    refine ⟨3237381191572237507954865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8633016510859300021212973 3237381191572237507954865)
                    ·
                      refine ⟨2428035893679178130966149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237381191572237507954865 2428035893679178130966149)
                      ·
                        rfl

theorem cell23_4728583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4728583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728583 prefixEnd_4728583 := by exact prefixLift 4728583
  have htrace : WordTrace (prefixWord ++ tailWord_4728583) baseStart_4728583 baseEnd_4728583 := by
    simpa [prefixWord, tailWord_4728583, baseEnd_4728583] using wordTrace_append hprefix tailTrace_4728583
  have hstable : (prefixWord ++ tailWord_4728583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728583).length < 2 ^ (prefixWord ++ tailWord_4728583).sum := by decide
  have hdescent : baseEnd_4728583 < baseStart_4728583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728599 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_4728599 : Nat := 118140960795 + 4728599 * 2 ^ 59
def prefixEnd_4728599 : Nat := 4983230072969 + 3 ^ 40 * 4728599 * 2
def baseEnd_4728599 : Nat := 2428044109369650068366075

theorem tailTrace_4728599 : CollatzResearch.WordTrace tailWord_4728599 prefixEnd_4728599 2428044109369650068366075 := by
  unfold tailWord_4728599
  simp only [CollatzResearch.WordTrace]
  refine ⟨172466174196100878259548851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114977449464067252173032567 172466174196100878259548851)
  ·
    refine ⟨258699261294151317389323277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172466174196100878259548851 258699261294151317389323277)
    ·
      refine ⟨97012222985306744020996229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258699261294151317389323277 97012222985306744020996229)
      ·
        refine ⟨18189791809745014503936793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97012222985306744020996229 18189791809745014503936793)
        ·
          refine ⟨13642343857308760877952595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18189791809745014503936793 13642343857308760877952595)
          ·
            refine ⟨20463515785963141316928893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13642343857308760877952595 20463515785963141316928893)
            ·
              refine ⟨7673818419736177993848335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20463515785963141316928893 7673818419736177993848335)
              ·
                refine ⟨11510727629604266990772503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7673818419736177993848335 11510727629604266990772503)
                ·
                  refine ⟨17266091444406400486158755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11510727629604266990772503 17266091444406400486158755)
                  ·
                    refine ⟨25899137166609600729238133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17266091444406400486158755 25899137166609600729238133)
                    ·
                      refine ⟨2428044109369650068366075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25899137166609600729238133 2428044109369650068366075)
                      ·
                        rfl

theorem cell23_4728599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_4728599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728599 prefixEnd_4728599 := by exact prefixLift 4728599
  have htrace : WordTrace (prefixWord ++ tailWord_4728599) baseStart_4728599 baseEnd_4728599 := by
    simpa [prefixWord, tailWord_4728599, baseEnd_4728599] using wordTrace_append hprefix tailTrace_4728599
  have hstable : (prefixWord ++ tailWord_4728599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728599).length < 2 ^ (prefixWord ++ tailWord_4728599).sum := by decide
  have hdescent : baseEnd_4728599 < baseStart_4728599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728630 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_4728630 : Nat := 118140960795 + 4728630 * 2 ^ 59
def prefixEnd_4728630 : Nat := 4983230072969 + 3 ^ 40 * 4728630 * 2
def baseEnd_4728630 : Nat := 2428060027269939447078433

theorem tailTrace_4728630 : CollatzResearch.WordTrace tailWord_4728630 prefixEnd_4728630 2428060027269939447078433 := by
  unfold tailWord_4728630
  simp only [CollatzResearch.WordTrace]
  refine ⟨10779206553686785659620459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114978203239325713702618229 10779206553686785659620459)
  ·
    refine ⟨16168809830530178489430689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10779206553686785659620459 16168809830530178489430689)
    ·
      refine ⟨12126607372897633867073017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16168809830530178489430689 12126607372897633867073017)
      ·
        refine ⟨9094955529673225400304763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12126607372897633867073017 9094955529673225400304763)
        ·
          refine ⟨13642433294509838100457145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9094955529673225400304763 13642433294509838100457145)
          ·
            refine ⟨10231824970882378575342859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13642433294509838100457145 10231824970882378575342859)
            ·
              refine ⟨15347737456323567863014289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10231824970882378575342859 15347737456323567863014289)
              ·
                refine ⟨11510803092242675897260717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15347737456323567863014289 11510803092242675897260717)
                ·
                  refine ⟨4316551159591003461472769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11510803092242675897260717 4316551159591003461472769)
                  ·
                    refine ⟨3237413369693252596104577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4316551159591003461472769 3237413369693252596104577)
                    ·
                      refine ⟨2428060027269939447078433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237413369693252596104577 2428060027269939447078433)
                      ·
                        rfl

theorem cell23_4728630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_4728630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728630 prefixEnd_4728630 := by exact prefixLift 4728630
  have htrace : WordTrace (prefixWord ++ tailWord_4728630) baseStart_4728630 baseEnd_4728630 := by
    simpa [prefixWord, tailWord_4728630, baseEnd_4728630] using wordTrace_append hprefix tailTrace_4728630
  have hstable : (prefixWord ++ tailWord_4728630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728630).length < 2 ^ (prefixWord ++ tailWord_4728630).sum := by decide
  have hdescent : baseEnd_4728630 < baseStart_4728630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728776 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_4728776 : Nat := 118140960795 + 4728776 * 2 ^ 59
def prefixEnd_4728776 : Nat := 4983230072969 + 3 ^ 40 * 4728776 * 2
def baseEnd_4728776 : Nat := 2428134995445495875852761

theorem tailTrace_4728776 : CollatzResearch.WordTrace tailWord_4728776 prefixEnd_4728776 2428134995445495875852761 := by
  unfold tailWord_4728776
  simp only [CollatzResearch.WordTrace]
  refine ⟨86236314958229818744371091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114981753277639758325828121 86236314958229818744371091)
  ·
    refine ⟨129354472437344728116556637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86236314958229818744371091 129354472437344728116556637)
    ·
      refine ⟨48507927164004273043708739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129354472437344728116556637 48507927164004273043708739)
      ·
        refine ⟨72761890746006409565563109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48507927164004273043708739 72761890746006409565563109)
        ·
          refine ⟨13642854514876201793543083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72761890746006409565563109 13642854514876201793543083)
          ·
            refine ⟨20464281772314302690314625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13642854514876201793543083 20464281772314302690314625)
            ·
              refine ⟨15348211329235727017735969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20464281772314302690314625 15348211329235727017735969)
              ·
                refine ⟨11511158496926795263301977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15348211329235727017735969 11511158496926795263301977)
                ·
                  refine ⟨8633368872695096447476483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11511158496926795263301977 8633368872695096447476483)
                  ·
                    refine ⟨12950053309042644671214725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8633368872695096447476483 12950053309042644671214725)
                    ·
                      refine ⟨2428134995445495875852761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12950053309042644671214725 2428134995445495875852761)
                      ·
                        rfl

theorem cell23_4728776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_4728776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728776 prefixEnd_4728776 := by exact prefixLift 4728776
  have htrace : WordTrace (prefixWord ++ tailWord_4728776) baseStart_4728776 baseEnd_4728776 := by
    simpa [prefixWord, tailWord_4728776, baseEnd_4728776] using wordTrace_append hprefix tailTrace_4728776
  have hstable : (prefixWord ++ tailWord_4728776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728776).length < 2 ^ (prefixWord ++ tailWord_4728776).sum := by decide
  have hdescent : baseEnd_4728776 < baseStart_4728776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728793 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 2, 4, 2]
def baseStart_4728793 : Nat := 118140960795 + 4728793 * 2 ^ 59
def prefixEnd_4728793 : Nat := 4983230072969 + 3 ^ 40 * 4728793 * 2
def baseEnd_4728793 : Nat := 2428143724616622309340183

theorem tailTrace_4728793 : CollatzResearch.WordTrace tailWord_4728793 prefixEnd_4728793 2428143724616622309340183 := by
  unfold tailWord_4728793
  simp only [CollatzResearch.WordTrace]
  refine ⟨172473249957398049392111033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114982166638265366261407355 172473249957398049392111033)
  ·
    refine ⟨129354937468048537044083275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172473249957398049392111033 129354937468048537044083275)
    ·
      refine ⟨194032406202072805566124913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129354937468048537044083275 194032406202072805566124913)
      ·
        refine ⟨145524304651554604174593685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194032406202072805566124913 145524304651554604174593685)
        ·
          refine ⟨6821451780541622070684079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145524304651554604174593685 6821451780541622070684079)
          ·
            refine ⟨10232177670812433106026119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6821451780541622070684079 10232177670812433106026119)
            ·
              refine ⟨15348266506218649659039179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10232177670812433106026119 15348266506218649659039179)
              ·
                refine ⟨23022399759327974488558769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15348266506218649659039179 23022399759327974488558769)
                ·
                  refine ⟨17266799819495980866419077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23022399759327974488558769 17266799819495980866419077)
                  ·
                    refine ⟨3237524966155496412453577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17266799819495980866419077 3237524966155496412453577)
                    ·
                      refine ⟨2428143724616622309340183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237524966155496412453577 2428143724616622309340183)
                      ·
                        rfl

theorem cell23_4728793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_4728793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728793 prefixEnd_4728793 := by exact prefixLift 4728793
  have htrace : WordTrace (prefixWord ++ tailWord_4728793) baseStart_4728793 baseEnd_4728793 := by
    simpa [prefixWord, tailWord_4728793, baseEnd_4728793] using wordTrace_append hprefix tailTrace_4728793
  have hstable : (prefixWord ++ tailWord_4728793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728793).length < 2 ^ (prefixWord ++ tailWord_4728793).sum := by decide
  have hdescent : baseEnd_4728793 < baseStart_4728793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728843 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 3]
def baseStart_4728843 : Nat := 118140960795 + 4728843 * 2 ^ 59
def prefixEnd_4728843 : Nat := 4983230072969 + 3 ^ 40 * 4728843 * 2
def baseEnd_4728843 : Nat := 2428169398649347113714953

theorem tailTrace_4728843 : CollatzResearch.WordTrace tailWord_4728843 prefixEnd_4728843 2428169398649347113714953 := by
  unfold tailWord_4728843
  simp only [CollatzResearch.WordTrace]
  refine ⟨172475073607216907931431183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114983382404811271954287455 172475073607216907931431183)
  ·
    refine ⟨258712610410825361897146775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172475073607216907931431183 258712610410825361897146775)
    ·
      refine ⟨388068915616238042845720163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258712610410825361897146775 388068915616238042845720163)
      ·
        refine ⟨582103373424357064268580245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388068915616238042845720163 582103373424357064268580245)
        ·
          refine ⟨27286095629266737387589699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 582103373424357064268580245 27286095629266737387589699)
          ·
            refine ⟨40929143443900106081384549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27286095629266737387589699 40929143443900106081384549)
            ·
              refine ⟨7674214395731269890259603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40929143443900106081384549 7674214395731269890259603)
              ·
                refine ⟨11511321593596904835389405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7674214395731269890259603 11511321593596904835389405)
                ·
                  refine ⟨4316745597598839313271027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11511321593596904835389405 4316745597598839313271027)
                  ·
                    refine ⟨6475118396398258969906541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4316745597598839313271027 6475118396398258969906541)
                    ·
                      refine ⟨2428169398649347113714953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475118396398258969906541 2428169398649347113714953)
                      ·
                        rfl

theorem cell23_4728843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 3].length) (baseStart_4728843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728843 prefixEnd_4728843 := by exact prefixLift 4728843
  have htrace : WordTrace (prefixWord ++ tailWord_4728843) baseStart_4728843 baseEnd_4728843 := by
    simpa [prefixWord, tailWord_4728843, baseEnd_4728843] using wordTrace_append hprefix tailTrace_4728843
  have hstable : (prefixWord ++ tailWord_4728843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728843).length < 2 ^ (prefixWord ++ tailWord_4728843).sum := by decide
  have hdescent : baseEnd_4728843 < baseStart_4728843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728859 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 1, 6]
def baseStart_4728859 : Nat := 118140960795 + 4728859 * 2 ^ 59
def prefixEnd_4728859 : Nat := 4983230072969 + 3 ^ 40 * 4728859 * 2
def baseEnd_4728859 : Nat := 809392538113273017038293

theorem tailTrace_4728859 : CollatzResearch.WordTrace tailWord_4728859 prefixEnd_4728859 809392538113273017038293 := by
  unfold tailWord_4728859
  simp only [CollatzResearch.WordTrace]
  refine ⟨172475657175158942664013631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114983771450105961776009087 172475657175158942664013631)
  ·
    refine ⟨258713485762738413996020447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172475657175158942664013631 258713485762738413996020447)
    ·
      refine ⟨388070228644107620994030671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258713485762738413996020447 388070228644107620994030671)
      ·
        refine ⟨582105342966161431491046007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388070228644107620994030671 582105342966161431491046007)
        ·
          refine ⟨873158014449242147236569011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582105342966161431491046007 873158014449242147236569011)
          ·
            refine ⟨1309737021673863220854853517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873158014449242147236569011 1309737021673863220854853517)
            ·
              refine ⟨491151383127698707820570069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1309737021673863220854853517 491151383127698707820570069)
              ·
                refine ⟨11511360542055438464544611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 491151383127698707820570069 11511360542055438464544611)
                ·
                  refine ⟨17267040813083157696816917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11511360542055438464544611 17267040813083157696816917)
                  ·
                    refine ⟨809392538113273017038293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17267040813083157696816917 809392538113273017038293)
                    ·
                      rfl

theorem cell23_4728859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 6].length) (baseStart_4728859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728859 prefixEnd_4728859 := by exact prefixLift 4728859
  have htrace : WordTrace (prefixWord ++ tailWord_4728859) baseStart_4728859 baseEnd_4728859 := by
    simpa [prefixWord, tailWord_4728859, baseEnd_4728859] using wordTrace_append hprefix tailTrace_4728859
  have hstable : (prefixWord ++ tailWord_4728859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728859).length < 2 ^ (prefixWord ++ tailWord_4728859).sum := by decide
  have hdescent : baseEnd_4728859 < baseStart_4728859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728883 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 5, 2, 2]
def baseStart_4728883 : Nat := 118140960795 + 4728883 * 2 ^ 59
def prefixEnd_4728883 : Nat := 4983230072969 + 3 ^ 40 * 4728883 * 2
def baseEnd_4728883 : Nat := 2428189937875526957214769

theorem tailTrace_4728883 : CollatzResearch.WordTrace tailWord_4728883 prefixEnd_4728883 2428189937875526957214769 := by
  unfold tailWord_4728883
  simp only [CollatzResearch.WordTrace]
  refine ⟨172476532527071994762887303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114984355018047996508591535 172476532527071994762887303)
  ·
    refine ⟨258714798790607992144330955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172476532527071994762887303 258714798790607992144330955)
    ·
      refine ⟨388072198185911988216496433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258714798790607992144330955 388072198185911988216496433)
      ·
        refine ⟨291054148639433991162372325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388072198185911988216496433 291054148639433991162372325)
        ·
          refine ⟨54572652869893873342944811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291054148639433991162372325 54572652869893873342944811)
          ·
            refine ⟨81858979304840810014417217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54572652869893873342944811 81858979304840810014417217)
            ·
              refine ⟨61394234478630607510812913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81858979304840810014417217 61394234478630607510812913)
              ·
                refine ⟨46045675858972955633109685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61394234478630607510812913 46045675858972955633109685)
                ·
                  refine ⟨4316782111778714590604033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46045675858972955633109685 4316782111778714590604033)
                  ·
                    refine ⟨3237586583834035942953025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4316782111778714590604033 3237586583834035942953025)
                    ·
                      refine ⟨2428189937875526957214769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237586583834035942953025 2428189937875526957214769)
                      ·
                        rfl

theorem cell23_4728883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 2, 2].length) (baseStart_4728883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728883 prefixEnd_4728883 := by exact prefixLift 4728883
  have htrace : WordTrace (prefixWord ++ tailWord_4728883) baseStart_4728883 baseEnd_4728883 := by
    simpa [prefixWord, tailWord_4728883, baseEnd_4728883] using wordTrace_append hprefix tailTrace_4728883
  have hstable : (prefixWord ++ tailWord_4728883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728883).length < 2 ^ (prefixWord ++ tailWord_4728883).sum := by decide
  have hdescent : baseEnd_4728883 < baseStart_4728883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728893 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_4728893 : Nat := 118140960795 + 4728893 * 2 ^ 59
def prefixEnd_4728893 : Nat := 4983230072969 + 3 ^ 40 * 4728893 * 2
def baseEnd_4728893 : Nat := 809398357560690639363241

theorem tailTrace_4728893 : CollatzResearch.WordTrace tailWord_4728893 prefixEnd_4728893 809398357560690639363241 := by
  unfold tailWord_4728893
  simp only [CollatzResearch.WordTrace]
  refine ⟨172476897257035766470751333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114984598171357177647167555 172476897257035766470751333)
  ·
    refine ⟨32339418235694206213265875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172476897257035766470751333 32339418235694206213265875)
    ·
      refine ⟨48509127353541309319898813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32339418235694206213265875 48509127353541309319898813)
      ·
        refine ⟨18190922757577990994962055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48509127353541309319898813 18190922757577990994962055)
        ·
          refine ⟨27286384136366986492443083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18190922757577990994962055 27286384136366986492443083)
          ·
            refine ⟨40929576204550479738664625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27286384136366986492443083 40929576204550479738664625)
            ·
              refine ⟨30697182153412859803998469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40929576204550479738664625 30697182153412859803998469)
              ·
                refine ⟨5755721653764911213249713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30697182153412859803998469 5755721653764911213249713)
                ·
                  refine ⟨4316791240323683409937285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5755721653764911213249713 4316791240323683409937285)
                  ·
                    refine ⟨809398357560690639363241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4316791240323683409937285 809398357560690639363241)
                    ·
                      rfl

theorem cell23_4728893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_4728893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728893 prefixEnd_4728893 := by exact prefixLift 4728893
  have htrace : WordTrace (prefixWord ++ tailWord_4728893) baseStart_4728893 baseEnd_4728893 := by
    simpa [prefixWord, tailWord_4728893, baseEnd_4728893] using wordTrace_append hprefix tailTrace_4728893
  have hstable : (prefixWord ++ tailWord_4728893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728893).length < 2 ^ (prefixWord ++ tailWord_4728893).sum := by decide
  have hdescent : baseEnd_4728893 < baseStart_4728893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728894 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_4728894 : Nat := 118140960795 + 4728894 * 2 ^ 59
def prefixEnd_4728894 : Nat := 4983230072969 + 3 ^ 40 * 4728894 * 2
def baseEnd_4728894 : Nat := 2428195586162726414177219

theorem tailTrace_4728894 : CollatzResearch.WordTrace tailWord_4728894 prefixEnd_4728894 2428195586162726414177219 := by
  unfold tailWord_4728894
  simp only [CollatzResearch.WordTrace]
  refine ⟨21559616716254017955192217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114984622486688095761025157 21559616716254017955192217)
  ·
    refine ⟨16169712537190513466394163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21559616716254017955192217 16169712537190513466394163)
    ·
      refine ⟨24254568805785770199591245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16169712537190513466394163 24254568805785770199591245)
      ·
        refine ⟨9095463302169663824846717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24254568805785770199591245 9095463302169663824846717)
        ·
          refine ⟨3410798738313623934317519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9095463302169663824846717 3410798738313623934317519)
          ·
            refine ⟨5116198107470435901476279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410798738313623934317519 5116198107470435901476279)
            ·
              refine ⟨7674297161205653852214419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5116198107470435901476279 7674297161205653852214419)
              ·
                refine ⟨11511445741808480778321629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7674297161205653852214419 11511445741808480778321629)
                ·
                  refine ⟨4316792153178180291870611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11511445741808480778321629 4316792153178180291870611)
                  ·
                    refine ⟨6475188229767270437805917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4316792153178180291870611 6475188229767270437805917)
                    ·
                      refine ⟨2428195586162726414177219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475188229767270437805917 2428195586162726414177219)
                      ·
                        rfl

theorem cell23_4728894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_4728894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728894 prefixEnd_4728894 := by exact prefixLift 4728894
  have htrace : WordTrace (prefixWord ++ tailWord_4728894) baseStart_4728894 baseEnd_4728894 := by
    simpa [prefixWord, tailWord_4728894, baseEnd_4728894] using wordTrace_append hprefix tailTrace_4728894
  have hstable : (prefixWord ++ tailWord_4728894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728894).length < 2 ^ (prefixWord ++ tailWord_4728894).sum := by decide
  have hdescent : baseEnd_4728894 < baseStart_4728894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728910 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_4728910 : Nat := 118140960795 + 4728910 * 2 ^ 59
def prefixEnd_4728910 : Nat := 4983230072969 + 3 ^ 40 * 4728910 * 2
def baseEnd_4728910 : Nat := 809401267284399450525715

theorem tailTrace_4728910 : CollatzResearch.WordTrace tailWord_4728910 prefixEnd_4728910 809401267284399450525715 := by
  unfold tailWord_4728910
  simp only [CollatzResearch.WordTrace]
  refine ⟨21559689662246772296765023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114985011531982785582746789 21559689662246772296765023)
  ·
    refine ⟨32339534493370158445147535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21559689662246772296765023 32339534493370158445147535)
    ·
      refine ⟨48509301740055237667721303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32339534493370158445147535 48509301740055237667721303)
      ·
        refine ⟨72763952610082856501581955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48509301740055237667721303 72763952610082856501581955)
        ·
          refine ⟨109145928915124284752372933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72763952610082856501581955 109145928915124284752372933)
          ·
            refine ⟨20464861671585803391069925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109145928915124284752372933 20464861671585803391069925)
            ·
              refine ⟨3837161563422338135825611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20464861671585803391069925 3837161563422338135825611)
              ·
                refine ⟨5755742345133507203738417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837161563422338135825611 5755742345133507203738417)
                ·
                  refine ⟨4316806758850130402803813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5755742345133507203738417 4316806758850130402803813)
                  ·
                    refine ⟨809401267284399450525715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4316806758850130402803813 809401267284399450525715)
                    ·
                      rfl

theorem cell23_4728910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_4728910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728910 prefixEnd_4728910 := by exact prefixLift 4728910
  have htrace : WordTrace (prefixWord ++ tailWord_4728910) baseStart_4728910 baseEnd_4728910 := by
    simpa [prefixWord, tailWord_4728910, baseEnd_4728910] using wordTrace_append hprefix tailTrace_4728910
  have hstable : (prefixWord ++ tailWord_4728910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728910).length < 2 ^ (prefixWord ++ tailWord_4728910).sum := by decide
  have hdescent : baseEnd_4728910 < baseStart_4728910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728920 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 1, 2, 3]
def baseStart_4728920 : Nat := 118140960795 + 4728920 * 2 ^ 59
def prefixEnd_4728920 : Nat := 4983230072969 + 3 ^ 40 * 4728920 * 2
def baseEnd_4728920 : Nat := 2428208936659743312452099

theorem tailTrace_4728920 : CollatzResearch.WordTrace tailWord_4728920 prefixEnd_4728920 2428208936659743312452099 := by
  unfold tailWord_4728920
  simp only [CollatzResearch.WordTrace]
  refine ⟨86238941013968975040992107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114985254685291966721322809 86238941013968975040992107)
  ·
    refine ⟨129358411520953462561488161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86238941013968975040992107 129358411520953462561488161)
    ·
      refine ⟨97018808640715096921116121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129358411520953462561488161 97018808640715096921116121)
      ·
        refine ⟨72764106480536322690837091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97018808640715096921116121 72764106480536322690837091)
        ·
          refine ⟨109146159720804484036255637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72764106480536322690837091 109146159720804484036255637)
          ·
            refine ⟨5116226236912710189199483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109146159720804484036255637 5116226236912710189199483)
            ·
              refine ⟨7674339355369065283799225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5116226236912710189199483 7674339355369065283799225)
              ·
                refine ⟨5755754516526798962849419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7674339355369065283799225 5755754516526798962849419)
                ·
                  refine ⟨8633631774790198444274129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5755754516526798962849419 8633631774790198444274129)
                  ·
                    refine ⟨6475223831092648833205597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8633631774790198444274129 6475223831092648833205597)
                    ·
                      refine ⟨2428208936659743312452099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475223831092648833205597 2428208936659743312452099)
                      ·
                        rfl

theorem cell23_4728920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_4728920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728920 prefixEnd_4728920 := by exact prefixLift 4728920
  have htrace : WordTrace (prefixWord ++ tailWord_4728920) baseStart_4728920 baseEnd_4728920 := by
    simpa [prefixWord, tailWord_4728920, baseEnd_4728920] using wordTrace_append hprefix tailTrace_4728920
  have hstable : (prefixWord ++ tailWord_4728920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728920).length < 2 ^ (prefixWord ++ tailWord_4728920).sum := by decide
  have hdescent : baseEnd_4728920 < baseStart_4728920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728930 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4728930 : Nat := 118140960795 + 4728930 * 2 ^ 59
def prefixEnd_4728930 : Nat := 4983230072969 + 3 ^ 40 * 4728930 * 2
def baseEnd_4728930 : Nat := 2428214071466288273327053

theorem tailTrace_4728930 : CollatzResearch.WordTrace tailWord_4728930 prefixEnd_4728930 2428214071466288273327053 := by
  unfold tailWord_4728930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43119561689475430447462061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114985497838601147859898829 43119561689475430447462061)
  ·
    refine ⟨16169835633553286417798273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43119561689475430447462061 16169835633553286417798273)
    ·
      refine ⟨12127376725164964813348705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16169835633553286417798273 12127376725164964813348705)
      ·
        refine ⟨9095532543873723610011529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12127376725164964813348705 9095532543873723610011529)
        ·
          refine ⟨6821649407905292707508647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9095532543873723610011529 6821649407905292707508647)
          ·
            refine ⟨10232474111857939061262971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6821649407905292707508647 10232474111857939061262971)
            ·
              refine ⟨15348711167786908591894457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10232474111857939061262971 15348711167786908591894457)
              ·
                refine ⟨11511533375840181443920843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15348711167786908591894457 11511533375840181443920843)
                ·
                  refine ⟨17267300063760272165881265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11511533375840181443920843 17267300063760272165881265)
                  ·
                    refine ⟨12950475047820204124410949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17267300063760272165881265 12950475047820204124410949)
                    ·
                      refine ⟨2428214071466288273327053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12950475047820204124410949 2428214071466288273327053)
                      ·
                        rfl

theorem cell23_4728930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4728930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728930 prefixEnd_4728930 := by exact prefixLift 4728930
  have htrace : WordTrace (prefixWord ++ tailWord_4728930) baseStart_4728930 baseEnd_4728930 := by
    simpa [prefixWord, tailWord_4728930, baseEnd_4728930] using wordTrace_append hprefix tailTrace_4728930
  have hstable : (prefixWord ++ tailWord_4728930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728930).length < 2 ^ (prefixWord ++ tailWord_4728930).sum := by decide
  have hdescent : baseEnd_4728930 < baseStart_4728930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728933 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 3]
def baseStart_4728933 : Nat := 118140960795 + 4728933 * 2 ^ 59
def prefixEnd_4728933 : Nat := 4983230072969 + 3 ^ 40 * 4728933 * 2
def baseEnd_4728933 : Nat := 2428215611908251761589539

theorem tailTrace_4728933 : CollatzResearch.WordTrace tailWord_4728933 prefixEnd_4728933 2428215611908251761589539 := by
  unfold tailWord_4728933
  simp only [CollatzResearch.WordTrace]
  refine ⟨172478356176890853302207453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114985570784593902201471635 172478356176890853302207453)
  ·
    refine ⟨64679383566334069988327795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172478356176890853302207453 64679383566334069988327795)
    ·
      refine ⟨97019075349501104982491693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64679383566334069988327795 97019075349501104982491693)
      ·
        refine ⟨36382153256062914368434385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97019075349501104982491693 36382153256062914368434385)
        ·
          refine ⟨27286614942047185776325789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36382153256062914368434385 27286614942047185776325789)
          ·
            refine ⟨10232480603267694666122171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27286614942047185776325789 10232480603267694666122171)
            ·
              refine ⟨15348720904901541999183257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10232480603267694666122171 15348720904901541999183257)
              ·
                refine ⟨11511540678676156499387443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15348720904901541999183257 11511540678676156499387443)
                ·
                  refine ⟨17267311018014234749081165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11511540678676156499387443 17267311018014234749081165)
                  ·
                    refine ⟨6475241631755338030905437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17267311018014234749081165 6475241631755338030905437)
                    ·
                      refine ⟨2428215611908251761589539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475241631755338030905437 2428215611908251761589539)
                      ·
                        rfl

theorem cell23_4728933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_4728933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728933 prefixEnd_4728933 := by exact prefixLift 4728933
  have htrace : WordTrace (prefixWord ++ tailWord_4728933) baseStart_4728933 baseEnd_4728933 := by
    simpa [prefixWord, tailWord_4728933, baseEnd_4728933] using wordTrace_append hprefix tailTrace_4728933
  have hstable : (prefixWord ++ tailWord_4728933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728933).length < 2 ^ (prefixWord ++ tailWord_4728933).sum := by decide
  have hdescent : baseEnd_4728933 < baseStart_4728933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728956 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 2, 3, 4]
def baseStart_4728956 : Nat := 118140960795 + 4728956 * 2 ^ 59
def prefixEnd_4728956 : Nat := 4983230072969 + 3 ^ 40 * 4728956 * 2
def baseEnd_4728956 : Nat := 2428227421963305171601933

theorem tailTrace_4728956 : CollatzResearch.WordTrace tailWord_4728956 prefixEnd_4728956 2428227421963305171601933 := by
  unfold tailWord_4728956
  simp only [CollatzResearch.WordTrace]
  refine ⟨86239597527903764115147361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114986130037205018820196481 86239597527903764115147361)
  ·
    refine ⟨64679698145927823086360521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86239597527903764115147361 64679698145927823086360521)
    ·
      refine ⟨48509773609445867314770391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64679698145927823086360521 48509773609445867314770391)
      ·
        refine ⟨72764660414168800972155587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48509773609445867314770391 72764660414168800972155587)
        ·
          refine ⟨109146990621253201458233381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72764660414168800972155587 109146990621253201458233381)
          ·
            refine ⟨20465060741484975273418759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109146990621253201458233381 20465060741484975273418759)
            ·
              refine ⟨30697591112227462910128139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20465060741484975273418759 30697591112227462910128139)
              ·
                refine ⟨46046386668341194365192209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30697591112227462910128139 46046386668341194365192209)
                ·
                  refine ⟨34534790001255895773894157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46046386668341194365192209 34534790001255895773894157)
                  ·
                    refine ⟨12950546250470960915210309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34534790001255895773894157 12950546250470960915210309)
                    ·
                      refine ⟨2428227421963305171601933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12950546250470960915210309 2428227421963305171601933)
                      ·
                        rfl

theorem cell23_4728956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_4728956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728956 prefixEnd_4728956 := by exact prefixLift 4728956
  have htrace : WordTrace (prefixWord ++ tailWord_4728956) baseStart_4728956 baseEnd_4728956 := by
    simpa [prefixWord, tailWord_4728956, baseEnd_4728956] using wordTrace_append hprefix tailTrace_4728956
  have hstable : (prefixWord ++ tailWord_4728956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728956).length < 2 ^ (prefixWord ++ tailWord_4728956).sum := by decide
  have hdescent : baseEnd_4728956 < baseStart_4728956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728976 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 3]
def baseStart_4728976 : Nat := 118140960795 + 4728976 * 2 ^ 59
def prefixEnd_4728976 : Nat := 4983230072969 + 3 ^ 40 * 4728976 * 2
def baseEnd_4728976 : Nat := 2428237691576395093351841

theorem tailTrace_4728976 : CollatzResearch.WordTrace tailWord_4728976 prefixEnd_4728976 2428237691576395093351841 := by
  unfold tailWord_4728976
  simp only [CollatzResearch.WordTrace]
  refine ⟨86239962257867535823011391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114986616343823381097348521 86239962257867535823011391)
  ·
    refine ⟨129359943386801303734517087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86239962257867535823011391 129359943386801303734517087)
    ·
      refine ⟨194039915080201955601775631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129359943386801303734517087 194039915080201955601775631)
      ·
        refine ⟨291059872620302933402663447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194039915080201955601775631 291059872620302933402663447)
        ·
          refine ⟨436589808930454400103995171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291059872620302933402663447 436589808930454400103995171)
          ·
            refine ⟨654884713395681600155992757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436589808930454400103995171 654884713395681600155992757)
            ·
              refine ⟨61395441880845150014624321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 654884713395681600155992757 61395441880845150014624321)
              ·
                refine ⟨46046581410633862510968241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61395441880845150014624321 46046581410633862510968241)
                ·
                  refine ⟨34534936057975396883226181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46046581410633862510968241 34534936057975396883226181)
                  ·
                    refine ⟨6475300510870386915604909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34534936057975396883226181 6475300510870386915604909)
                    ·
                      refine ⟨2428237691576395093351841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475300510870386915604909 2428237691576395093351841)
                      ·
                        rfl

theorem cell23_4728976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_4728976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728976 prefixEnd_4728976 := by exact prefixLift 4728976
  have htrace : WordTrace (prefixWord ++ tailWord_4728976) baseStart_4728976 baseEnd_4728976 := by
    simpa [prefixWord, tailWord_4728976, baseEnd_4728976] using wordTrace_append hprefix tailTrace_4728976
  have hstable : (prefixWord ++ tailWord_4728976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728976).length < 2 ^ (prefixWord ++ tailWord_4728976).sum := by decide
  have hdescent : baseEnd_4728976 < baseStart_4728976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4728994 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_4728994 : Nat := 118140960795 + 4728994 * 2 ^ 59
def prefixEnd_4728994 : Nat := 4983230072969 + 3 ^ 40 * 4728994 * 2
def baseEnd_4728994 : Nat := 2428246934228176022926759

theorem tailTrace_4728994 : CollatzResearch.WordTrace tailWord_4728994 prefixEnd_4728994 2428246934228176022926759 := by
  unfold tailWord_4728994
  simp only [CollatzResearch.WordTrace]
  refine ⟨43120145257417465180044509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114987054019779907146785357 43120145257417465180044509)
  ·
    refine ⟨16170054471531549442516691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43120145257417465180044509 16170054471531549442516691)
    ·
      refine ⟨24255081707297324163775037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16170054471531549442516691 24255081707297324163775037)
      ·
        refine ⟨9095655640236496561415639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24255081707297324163775037 9095655640236496561415639)
        ·
          refine ⟨13643483460354744842123459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9095655640236496561415639 13643483460354744842123459)
          ·
            refine ⟨20465225190532117263185189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13643483460354744842123459 20465225190532117263185189)
            ·
              refine ⟨3837229723224771986847223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20465225190532117263185189 3837229723224771986847223)
              ·
                refine ⟨5755844584837157980270835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837229723224771986847223 5755844584837157980270835)
                ·
                  refine ⟨8633766877255736970406253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5755844584837157980270835 8633766877255736970406253)
                  ·
                    refine ⟨3237662578970901363902345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8633766877255736970406253 3237662578970901363902345)
                    ·
                      refine ⟨2428246934228176022926759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237662578970901363902345 2428246934228176022926759)
                      ·
                        rfl

theorem cell23_4728994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_4728994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4728994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4728994 prefixEnd_4728994 := by exact prefixLift 4728994
  have htrace : WordTrace (prefixWord ++ tailWord_4728994) baseStart_4728994 baseEnd_4728994 := by
    simpa [prefixWord, tailWord_4728994, baseEnd_4728994] using wordTrace_append hprefix tailTrace_4728994
  have hstable : (prefixWord ++ tailWord_4728994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4728994).length < 2 ^ (prefixWord ++ tailWord_4728994).sum := by decide
  have hdescent : baseEnd_4728994 < baseStart_4728994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4728994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729024 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 2, 2, 2]
def baseStart_4729024 : Nat := 118140960795 + 4729024 * 2 ^ 59
def prefixEnd_4729024 : Nat := 4983230072969 + 3 ^ 40 * 4729024 * 2
def baseEnd_4729024 : Nat := 2428262338647810905551621

theorem tailTrace_4729024 : CollatzResearch.WordTrace tailWord_4729024 prefixEnd_4729024 2428262338647810905551621 := by
  unfold tailWord_4729024
  simp only [CollatzResearch.WordTrace]
  refine ⟨86240837609780587921885063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114987783479707450562513417 86240837609780587921885063)
  ·
    refine ⟨129361256414670881882827595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86240837609780587921885063 129361256414670881882827595)
    ·
      refine ⟨194041884622006322824241393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129361256414670881882827595 194041884622006322824241393)
      ·
        refine ⟨145531413466504742118181045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194041884622006322824241393 145531413466504742118181045)
        ·
          refine ⟨13643570012484819573579473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145531413466504742118181045 13643570012484819573579473)
          ·
            refine ⟨10232677509363614680184605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13643570012484819573579473 10232677509363614680184605)
            ·
              refine ⟨3837254066011355505069227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10232677509363614680184605 3837254066011355505069227)
              ·
                refine ⟨5755881099017033257603841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837254066011355505069227 5755881099017033257603841)
                ·
                  refine ⟨4316910824262774943202881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5755881099017033257603841 4316910824262774943202881)
                  ·
                    refine ⟨3237683118197081207402161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4316910824262774943202881 3237683118197081207402161)
                    ·
                      refine ⟨2428262338647810905551621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237683118197081207402161 2428262338647810905551621)
                      ·
                        rfl

theorem cell23_4729024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_4729024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729024 prefixEnd_4729024 := by exact prefixLift 4729024
  have htrace : WordTrace (prefixWord ++ tailWord_4729024) baseStart_4729024 baseEnd_4729024 := by
    simpa [prefixWord, tailWord_4729024, baseEnd_4729024] using wordTrace_append hprefix tailTrace_4729024
  have hstable : (prefixWord ++ tailWord_4729024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729024).length < 2 ^ (prefixWord ++ tailWord_4729024).sum := by decide
  have hdescent : baseEnd_4729024 < baseStart_4729024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729100 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 2, 2, 3]
def baseStart_4729100 : Nat := 118140960795 + 4729100 * 2 ^ 59
def prefixEnd_4729100 : Nat := 4983230072969 + 3 ^ 40 * 4729100 * 2
def baseEnd_4729100 : Nat := 2428301363177552608201271

theorem tailTrace_4729100 : CollatzResearch.WordTrace tailWord_4729100 prefixEnd_4729100 2428301363177552608201271 := by
  unfold tailWord_4729100
  simp only [CollatzResearch.WordTrace]
  refine ⟨86242223583642920411768377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114989631444857227215691169 86242223583642920411768377)
  ·
    refine ⟨64681667687732190308826283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86242223583642920411768377 64681667687732190308826283)
    ·
      refine ⟨97022501531598285463239425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64681667687732190308826283 97022501531598285463239425)
      ·
        refine ⟨72766876148698714097429569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97022501531598285463239425 72766876148698714097429569)
        ·
          refine ⟨54575157111524035573072177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72766876148698714097429569 54575157111524035573072177)
          ·
            refine ⟨40931367833643026679804133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54575157111524035573072177 40931367833643026679804133)
            ·
              refine ⟨7674631468808067502463275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40931367833643026679804133 7674631468808067502463275)
              ·
                refine ⟨11511947203212101253694913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7674631468808067502463275 11511947203212101253694913)
                ·
                  refine ⟨8633960402409075940271185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11511947203212101253694913 8633960402409075940271185)
                  ·
                    refine ⟨6475470301806806955203389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8633960402409075940271185 6475470301806806955203389)
                    ·
                      refine ⟨2428301363177552608201271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475470301806806955203389 2428301363177552608201271)
                      ·
                        rfl

theorem cell23_4729100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_4729100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729100 prefixEnd_4729100 := by exact prefixLift 4729100
  have htrace : WordTrace (prefixWord ++ tailWord_4729100) baseStart_4729100 baseEnd_4729100 := by
    simpa [prefixWord, tailWord_4729100, baseEnd_4729100] using wordTrace_append hprefix tailTrace_4729100
  have hstable : (prefixWord ++ tailWord_4729100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729100).length < 2 ^ (prefixWord ++ tailWord_4729100).sum := by decide
  have hdescent : baseEnd_4729100 < baseStart_4729100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729120 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 6]
def baseStart_4729120 : Nat := 118140960795 + 4729120 * 2 ^ 59
def prefixEnd_4729120 : Nat := 4983230072969 + 3 ^ 40 * 4729120 * 2
def baseEnd_4729120 : Nat := 269812403643404725550131

theorem tailTrace_4729120 : CollatzResearch.WordTrace tailWord_4729120 prefixEnd_4729120 269812403643404725550131 := by
  unfold tailWord_4729120
  simp only [CollatzResearch.WordTrace]
  refine ⟨86242588313606692119632407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114990117751475589492843209 86242588313606692119632407)
  ·
    refine ⟨129363882470410038179448611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86242588313606692119632407 129363882470410038179448611)
    ·
      refine ⟨194045823705615057269172917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129363882470410038179448611 194045823705615057269172917)
      ·
        refine ⟨18191795972401411618984961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194045823705615057269172917 18191795972401411618984961)
        ·
          refine ⟨13643846979301058714238721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18191795972401411618984961 13643846979301058714238721)
          ·
            refine ⟨10232885234475794035679041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13643846979301058714238721 10232885234475794035679041)
            ·
              refine ⟨7674663925856845526759281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10232885234475794035679041 7674663925856845526759281)
              ·
                refine ⟨5755997944392634145069461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7674663925856845526759281 5755997944392634145069461)
                ·
                  refine ⟨269812403643404725550131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5755997944392634145069461 269812403643404725550131)
                  ·
                    rfl

theorem cell23_4729120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 6].length) (baseStart_4729120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729120 prefixEnd_4729120 := by exact prefixLift 4729120
  have htrace : WordTrace (prefixWord ++ tailWord_4729120) baseStart_4729120 baseEnd_4729120 := by
    simpa [prefixWord, tailWord_4729120, baseEnd_4729120] using wordTrace_append hprefix tailTrace_4729120
  have hstable : (prefixWord ++ tailWord_4729120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729120).length < 2 ^ (prefixWord ++ tailWord_4729120).sum := by decide
  have hdescent : baseEnd_4729120 < baseStart_4729120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729124 : List Nat := [2, 3, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_4729124 : Nat := 118140960795 + 4729124 * 2 ^ 59
def prefixEnd_4729124 : Nat := 4983230072969 + 3 ^ 40 * 4729124 * 2
def baseEnd_4729124 : Nat := 809437895571086838100387

theorem tailTrace_4729124 : CollatzResearch.WordTrace tailWord_4729124 prefixEnd_4729124 809437895571086838100387 := by
  unfold tailWord_4729124
  simp only [CollatzResearch.WordTrace]
  refine ⟨86242661259599446461205213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114990215012799261948273617 86242661259599446461205213)
  ·
    refine ⟨32340997972349792422951955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86242661259599446461205213 32340997972349792422951955)
    ·
      refine ⟨48511496958524688634427933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32340997972349792422951955 48511496958524688634427933)
      ·
        refine ⟨18191811359446758237910475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48511496958524688634427933 18191811359446758237910475)
        ·
          refine ⟨27287717039170137356865713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18191811359446758237910475 27287717039170137356865713)
          ·
            refine ⟨20465787779377603017649285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27287717039170137356865713 20465787779377603017649285)
            ·
              refine ⟨3837335208633300565809241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20465787779377603017649285 3837335208633300565809241)
              ·
                refine ⟨2878001406474975424356931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3837335208633300565809241 2878001406474975424356931)
                ·
                  refine ⟨4317002109712463136535397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878001406474975424356931 4317002109712463136535397)
                  ·
                    refine ⟨809437895571086838100387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4317002109712463136535397 809437895571086838100387)
                    ·
                      rfl

theorem cell23_4729124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_4729124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729124 prefixEnd_4729124 := by exact prefixLift 4729124
  have htrace : WordTrace (prefixWord ++ tailWord_4729124) baseStart_4729124 baseEnd_4729124 := by
    simpa [prefixWord, tailWord_4729124, baseEnd_4729124] using wordTrace_append hprefix tailTrace_4729124
  have hstable : (prefixWord ++ tailWord_4729124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729124).length < 2 ^ (prefixWord ++ tailWord_4729124).sum := by decide
  have hdescent : baseEnd_4729124 < baseStart_4729124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729150 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4729150 : Nat := 118140960795 + 4729150 * 2 ^ 59
def prefixEnd_4729150 : Nat := 4983230072969 + 3 ^ 40 * 4729150 * 2
def baseEnd_4729150 : Nat := 809442345736759137525347

theorem tailTrace_4729150 : CollatzResearch.WordTrace tailWord_4729150 prefixEnd_4729150 809442345736759137525347 := by
  unfold tailWord_4729150
  simp only [CollatzResearch.WordTrace]
  refine ⟨21560783852138087420357113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114990847211403132908571269 21560783852138087420357113)
  ·
    refine ⟨16170587889103565565267835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21560783852138087420357113 16170587889103565565267835)
    ·
      refine ⟨24255881833655348347901753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16170587889103565565267835 24255881833655348347901753)
      ·
        refine ⟨18191911375241511260926315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24255881833655348347901753 18191911375241511260926315)
        ·
          refine ⟨27287867062862266891389473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18191911375241511260926315 27287867062862266891389473)
          ·
            refine ⟨20465900297146700168542105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27287867062862266891389473 20465900297146700168542105)
            ·
              refine ⟨15349425222860025126406579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20465900297146700168542105 15349425222860025126406579)
              ·
                refine ⟨23024137834290037689609869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15349425222860025126406579 23024137834290037689609869)
                ·
                  refine ⟨8634051687858764133603701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23024137834290037689609869 8634051687858764133603701)
                  ·
                    refine ⟨809442345736759137525347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8634051687858764133603701 809442345736759137525347)
                    ·
                      rfl

theorem cell23_4729150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4729150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729150 prefixEnd_4729150 := by exact prefixLift 4729150
  have htrace : WordTrace (prefixWord ++ tailWord_4729150) baseStart_4729150 baseEnd_4729150 := by
    simpa [prefixWord, tailWord_4729150, baseEnd_4729150] using wordTrace_append hprefix tailTrace_4729150
  have hstable : (prefixWord ++ tailWord_4729150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729150).length < 2 ^ (prefixWord ++ tailWord_4729150).sum := by decide
  have hdescent : baseEnd_4729150 < baseStart_4729150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729164 : List Nat := [2, 2, 1, 3, 2, 1, 4, 3, 1, 1, 3]
def baseStart_4729164 : Nat := 118140960795 + 4729164 * 2 ^ 59
def prefixEnd_4729164 : Nat := 4983230072969 + 3 ^ 40 * 4729164 * 2
def baseEnd_4729164 : Nat := 2428334225939440357800977

theorem tailTrace_4729164 : CollatzResearch.WordTrace tailWord_4729164 prefixEnd_4729164 2428334225939440357800977 := by
  unfold tailWord_4729164
  simp only [CollatzResearch.WordTrace]
  refine ⟨86243390719526989876933273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114991187626035986502577697 86243390719526989876933273)
  ·
    refine ⟨64682543039645242407699955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86243390719526989876933273 64682543039645242407699955)
    ·
      refine ⟨97023814559467863611549933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64682543039645242407699955 97023814559467863611549933)
      ·
        refine ⟨36383930459800448854331225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97023814559467863611549933 36383930459800448854331225)
        ·
          refine ⟨27287947844850336640748419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36383930459800448854331225 27287947844850336640748419)
          ·
            refine ⟨40931921767275504961122629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27287947844850336640748419 40931921767275504961122629)
            ·
              refine ⟨7674735331364157180210493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40931921767275504961122629 7674735331364157180210493)
              ·
                refine ⟨2878025749261558942578935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7674735331364157180210493 2878025749261558942578935)
                ·
                  refine ⟨4317038623892338413868403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878025749261558942578935 4317038623892338413868403)
                  ·
                    refine ⟨6475557935838507620802605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4317038623892338413868403 6475557935838507620802605)
                    ·
                      refine ⟨2428334225939440357800977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475557935838507620802605 2428334225939440357800977)
                      ·
                        rfl

theorem cell23_4729164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_4729164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729164 prefixEnd_4729164 := by exact prefixLift 4729164
  have htrace : WordTrace (prefixWord ++ tailWord_4729164) baseStart_4729164 baseEnd_4729164 := by
    simpa [prefixWord, tailWord_4729164, baseEnd_4729164] using wordTrace_append hprefix tailTrace_4729164
  have hstable : (prefixWord ++ tailWord_4729164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729164).length < 2 ^ (prefixWord ++ tailWord_4729164).sum := by decide
  have hdescent : baseEnd_4729164 < baseStart_4729164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729183 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_4729183 : Nat := 118140960795 + 4729183 * 2 ^ 59
def prefixEnd_4729183 : Nat := 4983230072969 + 3 ^ 40 * 4729183 * 2
def baseEnd_4729183 : Nat := 2428343982071875783463389

theorem tailTrace_4729183 : CollatzResearch.WordTrace tailWord_4729183 prefixEnd_4729183 2428343982071875783463389 := by
  unfold tailWord_4729183
  simp only [CollatzResearch.WordTrace]
  refine ⟨172487474425985145998808203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114991649617323430665872135 172487474425985145998808203)
  ·
    refine ⟨258731211638977718998212305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172487474425985145998808203 258731211638977718998212305)
    ·
      refine ⟨194048408729233289248659229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258731211638977718998212305 194048408729233289248659229)
      ·
        refine ⟨72768153273462483468247211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194048408729233289248659229 72768153273462483468247211)
        ·
          refine ⟨109152229910193725202370817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72768153273462483468247211 109152229910193725202370817)
          ·
            refine ⟨81864172432645293901778113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109152229910193725202370817 81864172432645293901778113)
            ·
              refine ⟨61398129324483970426333585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81864172432645293901778113 61398129324483970426333585)
              ·
                refine ⟨46048596993362977819750189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61398129324483970426333585 46048596993362977819750189)
                ·
                  refine ⟨17268223872511116682406321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46048596993362977819750189 17268223872511116682406321)
                  ·
                    refine ⟨12951167904383337511804741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17268223872511116682406321 12951167904383337511804741)
                    ·
                      refine ⟨2428343982071875783463389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12951167904383337511804741 2428343982071875783463389)
                      ·
                        rfl

theorem cell23_4729183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_4729183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729183 prefixEnd_4729183 := by exact prefixLift 4729183
  have htrace : WordTrace (prefixWord ++ tailWord_4729183) baseStart_4729183 baseEnd_4729183 := by
    simpa [prefixWord, tailWord_4729183, baseEnd_4729183] using wordTrace_append hprefix tailTrace_4729183
  have hstable : (prefixWord ++ tailWord_4729183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729183).length < 2 ^ (prefixWord ++ tailWord_4729183).sum := by decide
  have hdescent : baseEnd_4729183 < baseStart_4729183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729200 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 4]
def baseStart_4729200 : Nat := 118140960795 + 4729200 * 2 ^ 59
def prefixEnd_4729200 : Nat := 4983230072969 + 3 ^ 40 * 4729200 * 2
def baseEnd_4729200 : Nat := 2428352711243002216950811

theorem tailTrace_4729200 : CollatzResearch.WordTrace tailWord_4729200 prefixEnd_4729200 2428352711243002216950811 := by
  unfold tailWord_4729200
  simp only [CollatzResearch.WordTrace]
  refine ⟨86244047233461778951088527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114992062977949038601451369 86244047233461778951088527)
  ·
    refine ⟨129366070850192668426632791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86244047233461778951088527 129366070850192668426632791)
    ·
      refine ⟨194049106275289002639949187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129366070850192668426632791 194049106275289002639949187)
      ·
        refine ⟨291073659412933503959923781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194049106275289002639949187 291073659412933503959923781)
        ·
          refine ⟨54576311139925031992485709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291073659412933503959923781 54576311139925031992485709)
          ·
            refine ⟨20466116677471886997182141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54576311139925031992485709 20466116677471886997182141)
            ·
              refine ⟨7674793754051957623943303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20466116677471886997182141 7674793754051957623943303)
              ·
                refine ⟨11512190631077936435914955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7674793754051957623943303 11512190631077936435914955)
                ·
                  refine ⟨17268285946616904653872433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11512190631077936435914955 17268285946616904653872433)
                  ·
                    refine ⟨12951214459962678490404325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17268285946616904653872433 12951214459962678490404325)
                    ·
                      refine ⟨2428352711243002216950811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12951214459962678490404325 2428352711243002216950811)
                      ·
                        rfl

theorem cell23_4729200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_4729200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729200 prefixEnd_4729200 := by exact prefixLift 4729200
  have htrace : WordTrace (prefixWord ++ tailWord_4729200) baseStart_4729200 baseEnd_4729200 := by
    simpa [prefixWord, tailWord_4729200, baseEnd_4729200] using wordTrace_append hprefix tailTrace_4729200
  have hstable : (prefixWord ++ tailWord_4729200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729200).length < 2 ^ (prefixWord ++ tailWord_4729200).sum := by decide
  have hdescent : baseEnd_4729200 < baseStart_4729200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729220 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_4729220 : Nat := 118140960795 + 4729220 * 2 ^ 59
def prefixEnd_4729220 : Nat := 4983230072969 + 3 ^ 40 * 4729220 * 2
def baseEnd_4729220 : Nat := 2428362980856092138700719

theorem tailTrace_4729220 : CollatzResearch.WordTrace tailWord_4729220 prefixEnd_4729220 2428362980856092138700719 := by
  unfold tailWord_4729220
  simp only [CollatzResearch.WordTrace]
  refine ⟨86244411963425550658952557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114992549284567400878603409 86244411963425550658952557)
  ·
    refine ⟨32341654486284581497107209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86244411963425550658952557 32341654486284581497107209)
    ·
      refine ⟨24256240864713436122830407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32341654486284581497107209 24256240864713436122830407)
      ·
        refine ⟨36384361297070154184245611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24256240864713436122830407 36384361297070154184245611)
        ·
          refine ⟨54576541945605231276368417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36384361297070154184245611 54576541945605231276368417)
          ·
            refine ⟨40932406459203923457276313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54576541945605231276368417 40932406459203923457276313)
            ·
              refine ⟨30699304844402942592957235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40932406459203923457276313 30699304844402942592957235)
              ·
                refine ⟨46048957266604413889435853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30699304844402942592957235 46048957266604413889435853)
                ·
                  refine ⟨17268358974976655208538445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46048957266604413889435853 17268358974976655208538445)
                  ·
                    refine ⟨6475634615616245703201917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17268358974976655208538445 6475634615616245703201917)
                    ·
                      refine ⟨2428362980856092138700719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475634615616245703201917 2428362980856092138700719)
                      ·
                        rfl

theorem cell23_4729220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_4729220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729220 prefixEnd_4729220 := by exact prefixLift 4729220
  have htrace : WordTrace (prefixWord ++ tailWord_4729220) baseStart_4729220 baseEnd_4729220 := by
    simpa [prefixWord, tailWord_4729220, baseEnd_4729220] using wordTrace_append hprefix tailTrace_4729220
  have hstable : (prefixWord ++ tailWord_4729220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729220).length < 2 ^ (prefixWord ++ tailWord_4729220).sum := by decide
  have hdescent : baseEnd_4729220 < baseStart_4729220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729237 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_4729237 : Nat := 118140960795 + 4729237 * 2 ^ 59
def prefixEnd_4729237 : Nat := 4983230072969 + 3 ^ 40 * 4729237 * 2
def baseEnd_4729237 : Nat := 2428371710027218572188141

theorem tailTrace_4729237 : CollatzResearch.WordTrace tailWord_4729237 prefixEnd_4729237 2428371710027218572188141 := by
  unfold tailWord_4729237
  simp only [CollatzResearch.WordTrace]
  refine ⟨172489443967789513221273965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114992962645193008814182643 172489443967789513221273965)
  ·
    refine ⟨64683541487921067457977737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172489443967789513221273965 64683541487921067457977737)
    ·
      refine ⟨48512656115940800593483303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64683541487921067457977737 48512656115940800593483303)
      ·
        refine ⟨72768984173911200890224955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48512656115940800593483303 72768984173911200890224955)
        ·
          refine ⟨109153476260866801335337433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72768984173911200890224955 109153476260866801335337433)
          ·
            refine ⟨81865107195650101001503075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109153476260866801335337433 81865107195650101001503075)
            ·
              refine ⟨122797660793475151502254613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81865107195650101001503075 122797660793475151502254613)
              ·
                refine ⟨5756140349694147726668185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122797660793475151502254613 5756140349694147726668185)
                ·
                  refine ⟨4317105262270610795001139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5756140349694147726668185 4317105262270610795001139)
                  ·
                    refine ⟨6475657893405916192501709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4317105262270610795001139 6475657893405916192501709)
                    ·
                      refine ⟨2428371710027218572188141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475657893405916192501709 2428371710027218572188141)
                      ·
                        rfl

theorem cell23_4729237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_4729237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729237 prefixEnd_4729237 := by exact prefixLift 4729237
  have htrace : WordTrace (prefixWord ++ tailWord_4729237) baseStart_4729237 baseEnd_4729237 := by
    simpa [prefixWord, tailWord_4729237, baseEnd_4729237] using wordTrace_append hprefix tailTrace_4729237
  have hstable : (prefixWord ++ tailWord_4729237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729237).length < 2 ^ (prefixWord ++ tailWord_4729237).sum := by decide
  have hdescent : baseEnd_4729237 < baseStart_4729237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729247 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 3, 3, 2]
def baseStart_4729247 : Nat := 118140960795 + 4729247 * 2 ^ 59
def prefixEnd_4729247 : Nat := 4983230072969 + 3 ^ 40 * 4729247 * 2
def baseEnd_4729247 : Nat := 2428376844833763533063095

theorem tailTrace_4729247 : CollatzResearch.WordTrace tailWord_4729247 prefixEnd_4729247 2428376844833763533063095 := by
  unfold tailWord_4729247
  simp only [CollatzResearch.WordTrace]
  refine ⟨172489808697753284929137995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114993205798502189952758663 172489808697753284929137995)
  ·
    refine ⟨258734713046629927393706993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172489808697753284929137995 258734713046629927393706993)
    ·
      refine ⟨194051034784972445545280245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258734713046629927393706993 194051034784972445545280245)
      ·
        refine ⟨18192284511091166769870023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194051034784972445545280245 18192284511091166769870023)
        ·
          refine ⟨27288426766636750154805035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18192284511091166769870023 27288426766636750154805035)
          ·
            refine ⟨40932640149955125232207553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27288426766636750154805035 40932640149955125232207553)
            ·
              refine ⟨30699480112466343924155665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40932640149955125232207553 30699480112466343924155665)
              ·
                refine ⟨23024610084349757943116749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30699480112466343924155665 23024610084349757943116749)
                ·
                  refine ⟨8634228781631159228668781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23024610084349757943116749 8634228781631159228668781)
                  ·
                    refine ⟨3237835793111684710750793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8634228781631159228668781 3237835793111684710750793)
                    ·
                      refine ⟨2428376844833763533063095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237835793111684710750793 2428376844833763533063095)
                      ·
                        rfl

theorem cell23_4729247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_4729247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729247 prefixEnd_4729247 := by exact prefixLift 4729247
  have htrace : WordTrace (prefixWord ++ tailWord_4729247) baseStart_4729247 baseEnd_4729247 := by
    simpa [prefixWord, tailWord_4729247, baseEnd_4729247] using wordTrace_append hprefix tailTrace_4729247
  have hstable : (prefixWord ++ tailWord_4729247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729247).length < 2 ^ (prefixWord ++ tailWord_4729247).sum := by decide
  have hdescent : baseEnd_4729247 < baseStart_4729247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729253 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_4729253 : Nat := 118140960795 + 4729253 * 2 ^ 59
def prefixEnd_4729253 : Nat := 4983230072969 + 3 ^ 40 * 4729253 * 2
def baseEnd_4729253 : Nat := 809459975239230169862689

theorem tailTrace_4729253 : CollatzResearch.WordTrace tailWord_4729253 prefixEnd_4729253 809459975239230169862689 := by
  unfold tailWord_4729253
  simp only [CollatzResearch.WordTrace]
  refine ⟨172490027535731547953856413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114993351690487698635904275 172490027535731547953856413)
  ·
    refine ⟨64683760325899330482696155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172490027535731547953856413 64683760325899330482696155)
    ·
      refine ⟨97025640488848995724044233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64683760325899330482696155 97025640488848995724044233)
      ·
        refine ⟨72769230366636746793033175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97025640488848995724044233 72769230366636746793033175)
        ·
          refine ⟨109153845549955120189549763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72769230366636746793033175 109153845549955120189549763)
          ·
            refine ⟨163730768324932680284324645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109153845549955120189549763 163730768324932680284324645)
            ·
              refine ⟨30699519060924877553310871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163730768324932680284324645 30699519060924877553310871)
              ·
                refine ⟨46049278591387316329966307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30699519060924877553310871 46049278591387316329966307)
                ·
                  refine ⟨69073917887080974494949461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46049278591387316329966307 69073917887080974494949461)
                  ·
                    refine ⟨809459975239230169862689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69073917887080974494949461 809459975239230169862689)
                    ·
                      rfl

theorem cell23_4729253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_4729253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729253 prefixEnd_4729253 := by exact prefixLift 4729253
  have htrace : WordTrace (prefixWord ++ tailWord_4729253) baseStart_4729253 baseEnd_4729253 := by
    simpa [prefixWord, tailWord_4729253, baseEnd_4729253] using wordTrace_append hprefix tailTrace_4729253
  have hstable : (prefixWord ++ tailWord_4729253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729253).length < 2 ^ (prefixWord ++ tailWord_4729253).sum := by decide
  have hdescent : baseEnd_4729253 < baseStart_4729253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729277 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_4729277 : Nat := 118140960795 + 4729277 * 2 ^ 59
def prefixEnd_4729277 : Nat := 4983230072969 + 3 ^ 40 * 4729277 * 2
def baseEnd_4729277 : Nat := 2428392249253398415687957

theorem tailTrace_4729277 : CollatzResearch.WordTrace tailWord_4729277 prefixEnd_4729277 2428392249253398415687957 := by
  unfold tailWord_4729277
  simp only [CollatzResearch.WordTrace]
  refine ⟨172490902887644600052730085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114993935258429733368486723 172490902887644600052730085)
  ·
    refine ⟨32342044291433362509886891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172490902887644600052730085 32342044291433362509886891)
    ·
      refine ⟨48513066437150043764830337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32342044291433362509886891 48513066437150043764830337)
      ·
        refine ⟨36384799827862532823622753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48513066437150043764830337 36384799827862532823622753)
        ·
          refine ⟨27288599870896899617717065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36384799827862532823622753 27288599870896899617717065)
          ·
            refine ⟨20466449903172674713287799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27288599870896899617717065 20466449903172674713287799)
            ·
              refine ⟨30699674854759012069931699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20466449903172674713287799 30699674854759012069931699)
              ·
                refine ⟨46049512282138518104897549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30699674854759012069931699 46049512282138518104897549)
                ·
                  refine ⟨17268567105801944289336581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46049512282138518104897549 17268567105801944289336581)
                  ·
                    refine ⟨3237856332337864554250609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17268567105801944289336581 3237856332337864554250609)
                    ·
                      refine ⟨2428392249253398415687957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3237856332337864554250609 2428392249253398415687957)
                      ·
                        rfl

theorem cell23_4729277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_4729277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729277 prefixEnd_4729277 := by exact prefixLift 4729277
  have htrace : WordTrace (prefixWord ++ tailWord_4729277) baseStart_4729277 baseEnd_4729277 := by
    simpa [prefixWord, tailWord_4729277, baseEnd_4729277] using wordTrace_append hprefix tailTrace_4729277
  have hstable : (prefixWord ++ tailWord_4729277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729277).length < 2 ^ (prefixWord ++ tailWord_4729277).sum := by decide
  have hdescent : baseEnd_4729277 < baseStart_4729277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729290 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_4729290 : Nat := 118140960795 + 4729290 * 2 ^ 59
def prefixEnd_4729290 : Nat := 4983230072969 + 3 ^ 40 * 4729290 * 2
def baseEnd_4729290 : Nat := 2428398924501906864825397

theorem tailTrace_4729290 : CollatzResearch.WordTrace tailWord_4729290 prefixEnd_4729290 2428398924501906864825397 := by
  unfold tailWord_4729290
  simp only [CollatzResearch.WordTrace]
  refine ⟨43122844259149375818238331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114994251357731668848635549 43122844259149375818238331)
  ·
    refine ⟨64684266388724063727357497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43122844259149375818238331 64684266388724063727357497)
    ·
      refine ⟨48513199791543047795518123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64684266388724063727357497 48513199791543047795518123)
      ·
        refine ⟨72769799687314571693277185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48513199791543047795518123 72769799687314571693277185)
        ·
          refine ⟨54577349765485928769957889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72769799687314571693277185 54577349765485928769957889)
          ·
            refine ⟨40933012324114446577468417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54577349765485928769957889 40933012324114446577468417)
            ·
              refine ⟨30699759243085834933101313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40933012324114446577468417 30699759243085834933101313)
              ·
                refine ⟨23024819432314376199825985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30699759243085834933101313 23024819432314376199825985)
                ·
                  refine ⟨17268614574235782149869489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23024819432314376199825985 17268614574235782149869489)
                  ·
                    refine ⟨12951460930676836612402117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17268614574235782149869489 12951460930676836612402117)
                    ·
                      refine ⟨2428398924501906864825397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12951460930676836612402117 2428398924501906864825397)
                      ·
                        rfl

theorem cell23_4729290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_4729290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729290 prefixEnd_4729290 := by exact prefixLift 4729290
  have htrace : WordTrace (prefixWord ++ tailWord_4729290) baseStart_4729290 baseEnd_4729290 := by
    simpa [prefixWord, tailWord_4729290, baseEnd_4729290] using wordTrace_append hprefix tailTrace_4729290
  have hstable : (prefixWord ++ tailWord_4729290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729290).length < 2 ^ (prefixWord ++ tailWord_4729290).sum := by decide
  have hdescent : baseEnd_4729290 < baseStart_4729290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729303 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_4729303 : Nat := 118140960795 + 4729303 * 2 ^ 59
def prefixEnd_4729303 : Nat := 4983230072969 + 3 ^ 40 * 4729303 * 2
def baseEnd_4729303 : Nat := 2428405599750415313962837

theorem tailTrace_4729303 : CollatzResearch.WordTrace tailWord_4729303 prefixEnd_4729303 2428405599750415313962837 := by
  unfold tailWord_4729303
  simp only [CollatzResearch.WordTrace]
  refine ⟨172491851185550406493176563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114994567457033604328784375 172491851185550406493176563)
  ·
    refine ⟨258737776778325609739764845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172491851185550406493176563 258737776778325609739764845)
    ·
      refine ⟨97026666291872103652411817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258737776778325609739764845 97026666291872103652411817)
      ·
        refine ⟨72769999718904077739308863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97026666291872103652411817 72769999718904077739308863)
        ·
          refine ⟨109154999578356116608963295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72769999718904077739308863 109154999578356116608963295)
          ·
            refine ⟨163732499367534174913444943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109154999578356116608963295 163732499367534174913444943)
            ·
              refine ⟨245598749051301262370167415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163732499367534174913444943 245598749051301262370167415)
              ·
                refine ⟨368398123576951893555251123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245598749051301262370167415 368398123576951893555251123)
                ·
                  refine ⟨552597185365427840332876685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368398123576951893555251123 552597185365427840332876685)
                  ·
                    refine ⟨207223944512035440124828757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552597185365427840332876685 207223944512035440124828757)
                    ·
                      refine ⟨2428405599750415313962837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 207223944512035440124828757 2428405599750415313962837)
                      ·
                        rfl

theorem cell23_4729303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_4729303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729303 prefixEnd_4729303 := by exact prefixLift 4729303
  have htrace : WordTrace (prefixWord ++ tailWord_4729303) baseStart_4729303 baseEnd_4729303 := by
    simpa [prefixWord, tailWord_4729303, baseEnd_4729303] using wordTrace_append hprefix tailTrace_4729303
  have hstable : (prefixWord ++ tailWord_4729303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729303).length < 2 ^ (prefixWord ++ tailWord_4729303).sum := by decide
  have hdescent : baseEnd_4729303 < baseStart_4729303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729317 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 7]
def baseStart_4729317 : Nat := 118140960795 + 4729317 * 2 ^ 59
def prefixEnd_4729317 : Nat := 4983230072969 + 3 ^ 40 * 4729317 * 2
def baseEnd_4729317 : Nat := 269823643164397584354197

theorem tailTrace_4729317 : CollatzResearch.WordTrace tailWord_4729317 prefixEnd_4729317 269823643164397584354197 := by
  unfold tailWord_4729317
  simp only [CollatzResearch.WordTrace]
  refine ⟨172492361807499686884186205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114994907871666457922790803 172492361807499686884186205)
  ·
    refine ⟨64684635677812382581569827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172492361807499686884186205 64684635677812382581569827)
    ·
      refine ⟨97026953516718573872354741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64684635677812382581569827 97026953516718573872354741)
      ·
        refine ⟨9096276892192366300533257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97026953516718573872354741 9096276892192366300533257)
        ·
          refine ⟨6822207669144274725399943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9096276892192366300533257 6822207669144274725399943)
          ·
            refine ⟨10233311503716412088099915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6822207669144274725399943 10233311503716412088099915)
            ·
              refine ⟨15349967255574618132149873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10233311503716412088099915 15349967255574618132149873)
              ·
                refine ⟨11512475441680963599112405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15349967255574618132149873 11512475441680963599112405)
                ·
                  refine ⟨269823643164397584354197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11512475441680963599112405 269823643164397584354197)
                  ·
                    rfl

theorem cell23_4729317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_4729317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729317 prefixEnd_4729317 := by exact prefixLift 4729317
  have htrace : WordTrace (prefixWord ++ tailWord_4729317) baseStart_4729317 baseEnd_4729317 := by
    simpa [prefixWord, tailWord_4729317, baseEnd_4729317] using wordTrace_append hprefix tailTrace_4729317
  have hstable : (prefixWord ++ tailWord_4729317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729317).length < 2 ^ (prefixWord ++ tailWord_4729317).sum := by decide
  have hdescent : baseEnd_4729317 < baseStart_4729317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729334 : List Nat := [5, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_4729334 : Nat := 118140960795 + 4729334 * 2 ^ 59
def prefixEnd_4729334 : Nat := 4983230072969 + 3 ^ 40 * 4729334 * 2
def baseEnd_4729334 : Nat := 269824613072300521408355

theorem tailTrace_4729334 : CollatzResearch.WordTrace tailWord_4729334 prefixEnd_4729334 269824613072300521408355 := by
  unfold tailWord_4729334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10780811365527381174222191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114995321232292065858370037 10780811365527381174222191)
  ·
    refine ⟨16171217048291071761333287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10780811365527381174222191 16171217048291071761333287)
    ·
      refine ⟨24256825572436607641999931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16171217048291071761333287 24256825572436607641999931)
      ·
        refine ⟨36385238358654911462999897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24256825572436607641999931 36385238358654911462999897)
        ·
          refine ⟨27288928768991183597249923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36385238358654911462999897 27288928768991183597249923)
          ·
            refine ⟨40933393153486775395874885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27288928768991183597249923 40933393153486775395874885)
            ·
              refine ⟨7675011216278770386726541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40933393153486775395874885 7675011216278770386726541)
              ·
                refine ⟨2878129206104538895022453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7675011216278770386726541 2878129206104538895022453)
                ·
                  refine ⟨269824613072300521408355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2878129206104538895022453 269824613072300521408355)
                  ·
                    rfl

theorem cell23_4729334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_4729334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729334 prefixEnd_4729334 := by exact prefixLift 4729334
  have htrace : WordTrace (prefixWord ++ tailWord_4729334) baseStart_4729334 baseEnd_4729334 := by
    simpa [prefixWord, tailWord_4729334, baseEnd_4729334] using wordTrace_append hprefix tailTrace_4729334
  have hstable : (prefixWord ++ tailWord_4729334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729334).length < 2 ^ (prefixWord ++ tailWord_4729334).sum := by decide
  have hdescent : baseEnd_4729334 < baseStart_4729334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729377 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 3, 4]
def baseStart_4729377 : Nat := 118140960795 + 4729377 * 2 ^ 59
def prefixEnd_4729377 : Nat := 4983230072969 + 3 ^ 40 * 4729377 * 2
def baseEnd_4729377 : Nat := 809481199106282674812499

theorem tailTrace_4729377 : CollatzResearch.WordTrace tailWord_4729377 prefixEnd_4729377 809481199106282674812499 := by
  unfold tailWord_4729377
  simp only [CollatzResearch.WordTrace]
  refine ⟨172494550187282317131370385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114996366791521544754246923 172494550187282317131370385)
  ·
    refine ⟨129370912640461737848527789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172494550187282317131370385 129370912640461737848527789)
    ·
      refine ⟨48514092240173151693197921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129370912640461737848527789 48514092240173151693197921)
      ·
        refine ⟨36385569180129863769898441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48514092240173151693197921 36385569180129863769898441)
        ·
          refine ⟨27289176885097397827423831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36385569180129863769898441 27289176885097397827423831)
          ·
            refine ⟨40933765327646096741135747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27289176885097397827423831 40933765327646096741135747)
            ·
              refine ⟨61400647991469145111703621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40933765327646096741135747 61400647991469145111703621)
              ·
                refine ⟨11512621498400464708444429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61400647991469145111703621 11512621498400464708444429)
                ·
                  refine ⟨4317233061900174265666661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11512621498400464708444429 4317233061900174265666661)
                  ·
                    refine ⟨809481199106282674812499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4317233061900174265666661 809481199106282674812499)
                    ·
                      rfl

theorem cell23_4729377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_4729377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729377 prefixEnd_4729377 := by exact prefixLift 4729377
  have htrace : WordTrace (prefixWord ++ tailWord_4729377) baseStart_4729377 baseEnd_4729377 := by
    simpa [prefixWord, tailWord_4729377, baseEnd_4729377] using wordTrace_append hprefix tailTrace_4729377
  have hstable : (prefixWord ++ tailWord_4729377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729377).length < 2 ^ (prefixWord ++ tailWord_4729377).sum := by decide
  have hdescent : baseEnd_4729377 < baseStart_4729377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729404 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 2, 2, 3]
def baseStart_4729404 : Nat := 118140960795 + 4729404 * 2 ^ 59
def prefixEnd_4729404 : Nat := 4983230072969 + 3 ^ 40 * 4729404 * 2
def baseEnd_4729404 : Nat := 2428457461296519418799873

theorem tailTrace_4729404 : CollatzResearch.WordTrace tailWord_4729404 prefixEnd_4729404 2428457461296519418799873 := by
  unfold tailWord_4729404
  simp only [CollatzResearch.WordTrace]
  refine ⟨86247767479092250371301633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114997023305456333828402177 86247767479092250371301633)
  ·
    refine ⟨64685825609319187778476225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86247767479092250371301633 64685825609319187778476225)
    ·
      refine ⟨48514369206989390833857169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64685825609319187778476225 48514369206989390833857169)
      ·
        refine ⟨36385776905242043125392877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48514369206989390833857169 36385776905242043125392877)
        ·
          refine ⟨13644666339465766172022329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36385776905242043125392877 13644666339465766172022329)
          ·
            refine ⟨10233499754599324629016747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13644666339465766172022329 10233499754599324629016747)
            ·
              refine ⟨15350249631898986943525121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10233499754599324629016747 15350249631898986943525121)
              ·
                refine ⟨11512687223924240207643841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15350249631898986943525121 11512687223924240207643841)
                ·
                  refine ⟨8634515417943180155732881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11512687223924240207643841 8634515417943180155732881)
                  ·
                    refine ⟨6475886563457385116799661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8634515417943180155732881 6475886563457385116799661)
                    ·
                      refine ⟨2428457461296519418799873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475886563457385116799661 2428457461296519418799873)
                      ·
                        rfl

theorem cell23_4729404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_4729404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729404 prefixEnd_4729404 := by exact prefixLift 4729404
  have htrace : WordTrace (prefixWord ++ tailWord_4729404) baseStart_4729404 baseEnd_4729404 := by
    simpa [prefixWord, tailWord_4729404, baseEnd_4729404] using wordTrace_append hprefix tailTrace_4729404
  have hstable : (prefixWord ++ tailWord_4729404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729404).length < 2 ^ (prefixWord ++ tailWord_4729404).sum := by decide
  have hdescent : baseEnd_4729404 < baseStart_4729404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729462 : List Nat := [5, 1, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_4729462 : Nat := 118140960795 + 4729462 * 2 ^ 59
def prefixEnd_4729462 : Nat := 4983230072969 + 3 ^ 40 * 4729462 * 2
def baseEnd_4729462 : Nat := 809495747724826730624869

theorem tailTrace_4729462 : CollatzResearch.WordTrace tailWord_4729462 prefixEnd_4729462 809495747724826730624869 := by
  unfold tailWord_4729462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10781103149498398540513415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114998433594649584432143093 10781103149498398540513415)
  ·
    refine ⟨16171654724247597810770123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10781103149498398540513415 16171654724247597810770123)
    ·
      refine ⟨24257482086371396716155185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16171654724247597810770123 24257482086371396716155185)
      ·
        refine ⟨18193111564778547537116389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24257482086371396716155185 18193111564778547537116389)
        ·
          refine ⟨3411208418395977663209323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18193111564778547537116389 3411208418395977663209323)
          ·
            refine ⟨5116812627593966494813985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411208418395977663209323 5116812627593966494813985)
            ·
              refine ⟨3837609470695474871110489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5116812627593966494813985 3837609470695474871110489)
              ·
                refine ⟨2878207103021606153332867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3837609470695474871110489 2878207103021606153332867)
                ·
                  refine ⟨4317310654532409229999301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878207103021606153332867 4317310654532409229999301)
                  ·
                    refine ⟨809495747724826730624869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4317310654532409229999301 809495747724826730624869)
                    ·
                      rfl

theorem cell23_4729462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_4729462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729462 prefixEnd_4729462 := by exact prefixLift 4729462
  have htrace : WordTrace (prefixWord ++ tailWord_4729462) baseStart_4729462 baseEnd_4729462 := by
    simpa [prefixWord, tailWord_4729462, baseEnd_4729462] using wordTrace_append hprefix tailTrace_4729462
  have hstable : (prefixWord ++ tailWord_4729462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729462).length < 2 ^ (prefixWord ++ tailWord_4729462).sum := by decide
  have hdescent : baseEnd_4729462 < baseStart_4729462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729468 : List Nat := [2, 2, 2, 1, 1, 2, 6, 2, 1, 1, 3]
def baseStart_4729468 : Nat := 118140960795 + 4729468 * 2 ^ 59
def prefixEnd_4729468 : Nat := 4983230072969 + 3 ^ 40 * 4729468 * 2
def baseEnd_4729468 : Nat := 2428490324058407168399579

theorem tailTrace_4729468 : CollatzResearch.WordTrace tailWord_4729468 prefixEnd_4729468 2428490324058407168399579 := by
  unfold tailWord_4729468
  simp only [CollatzResearch.WordTrace]
  refine ⟨86248934614976319836466529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114998579486635093115288705 86248934614976319836466529)
  ·
    refine ⟨64686700961232239877349897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86248934614976319836466529 64686700961232239877349897)
    ·
      refine ⟨48515025720924179908012423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64686700961232239877349897 48515025720924179908012423)
      ·
        refine ⟨72772538581386269862018635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48515025720924179908012423 72772538581386269862018635)
        ·
          refine ⟨109158807872079404793027953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72772538581386269862018635 109158807872079404793027953)
          ·
            refine ⟨81869105904059553594770965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109158807872079404793027953 81869105904059553594770965)
            ·
              refine ⟨3837614339252791574754889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81869105904059553594770965 3837614339252791574754889)
              ·
                refine ⟨2878210754439593681066167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3837614339252791574754889 2878210754439593681066167)
                ·
                  refine ⟨4317316131659390521599251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878210754439593681066167 4317316131659390521599251)
                  ·
                    refine ⟨6475974197489085782398877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4317316131659390521599251 6475974197489085782398877)
                    ·
                      refine ⟨2428490324058407168399579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6475974197489085782398877 2428490324058407168399579)
                      ·
                        rfl

theorem cell23_4729468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_4729468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729468 prefixEnd_4729468 := by exact prefixLift 4729468
  have htrace : WordTrace (prefixWord ++ tailWord_4729468) baseStart_4729468 baseEnd_4729468 := by
    simpa [prefixWord, tailWord_4729468, baseEnd_4729468] using wordTrace_append hprefix tailTrace_4729468
  have hstable : (prefixWord ++ tailWord_4729468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729468).length < 2 ^ (prefixWord ++ tailWord_4729468).sum := by decide
  have hdescent : baseEnd_4729468 < baseStart_4729468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729497 : List Nat := [1, 2, 1, 2, 1, 2, 7, 7]
def baseStart_4729497 : Nat := 118140960795 + 4729497 * 2 ^ 59
def prefixEnd_4729497 : Nat := 4983230072969 + 3 ^ 40 * 4729497 * 2
def baseEnd_4729497 : Nat := 89944637592495835368035

theorem tailTrace_4729497 : CollatzResearch.WordTrace tailWord_4729497 prefixEnd_4729497 89944637592495835368035 := by
  unfold tailWord_4729497
  simp only [CollatzResearch.WordTrace]
  refine ⟨172498926946847577625738745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114999284631231718417159163 172498926946847577625738745)
  ·
    refine ⟨129374195210135683219304059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172498926946847577625738745 129374195210135683219304059)
    ·
      refine ⟨194061292815203524828956089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129374195210135683219304059 194061292815203524828956089)
      ·
        refine ⟨145545969611402643621717067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194061292815203524828956089 145545969611402643621717067)
        ·
          refine ⟨218318954417103965432575601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145545969611402643621717067 218318954417103965432575601)
          ·
            refine ⟨163739215812827974074431701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218318954417103965432575601 163739215812827974074431701)
            ·
              refine ⟨3837637870613155642369493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 163739215812827974074431701 3837637870613155642369493)
              ·
                refine ⟨89944637592495835368035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3837637870613155642369493 89944637592495835368035)
                ·
                  rfl

theorem cell23_4729497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 7].length) (baseStart_4729497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729497 prefixEnd_4729497 := by exact prefixLift 4729497
  have htrace : WordTrace (prefixWord ++ tailWord_4729497) baseStart_4729497 baseEnd_4729497 := by
    simpa [prefixWord, tailWord_4729497, baseEnd_4729497] using wordTrace_append hprefix tailTrace_4729497
  have hstable : (prefixWord ++ tailWord_4729497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729497).length < 2 ^ (prefixWord ++ tailWord_4729497).sum := by decide
  have hdescent : baseEnd_4729497 < baseStart_4729497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729507 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 3]
def baseStart_4729507 : Nat := 118140960795 + 4729507 * 2 ^ 59
def prefixEnd_4729507 : Nat := 4983230072969 + 3 ^ 40 * 4729507 * 2
def baseEnd_4729507 : Nat := 2428510349803932515811899

theorem tailTrace_4729507 : CollatzResearch.WordTrace tailWord_4729507 prefixEnd_4729507 2428510349803932515811899 := by
  unfold tailWord_4729507
  simp only [CollatzResearch.WordTrace]
  refine ⟨172499291676811349333602775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114999527784540899555735183 172499291676811349333602775)
  ·
    refine ⟨258748937515217024000404163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172499291676811349333602775 258748937515217024000404163)
    ·
      refine ⟨388123406272825536000606245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258748937515217024000404163 388123406272825536000606245)
      ·
        refine ⟨72773138676154788000113671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 388123406272825536000606245 72773138676154788000113671)
        ·
          refine ⟨109159708014232182000170507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72773138676154788000113671 109159708014232182000170507)
          ·
            refine ⟨163739562021348273000255761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109159708014232182000170507 163739562021348273000255761)
            ·
              refine ⟨122804671516011204750191821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163739562021348273000255761 122804671516011204750191821)
              ·
                refine ⟨46051751818504201781321933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122804671516011204750191821 46051751818504201781321933)
                ·
                  refine ⟨17269406931939075667995725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46051751818504201781321933 17269406931939075667995725)
                  ·
                    refine ⟨6476027599477153375498397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17269406931939075667995725 6476027599477153375498397)
                    ·
                      refine ⟨2428510349803932515811899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6476027599477153375498397 2428510349803932515811899)
                      ·
                        rfl

theorem cell23_4729507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_4729507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729507 prefixEnd_4729507 := by exact prefixLift 4729507
  have htrace : WordTrace (prefixWord ++ tailWord_4729507) baseStart_4729507 baseEnd_4729507 := by
    simpa [prefixWord, tailWord_4729507, baseEnd_4729507] using wordTrace_append hprefix tailTrace_4729507
  have hstable : (prefixWord ++ tailWord_4729507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729507).length < 2 ^ (prefixWord ++ tailWord_4729507).sum := by decide
  have hdescent : baseEnd_4729507 < baseStart_4729507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729518 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4729518 : Nat := 118140960795 + 4729518 * 2 ^ 59
def prefixEnd_4729518 : Nat := 4983230072969 + 3 ^ 40 * 4729518 * 2
def baseEnd_4729518 : Nat := 809505332697043990924783

theorem tailTrace_4729518 : CollatzResearch.WordTrace tailWord_4729518 prefixEnd_4729518 809505332697043990924783 := by
  unfold tailWord_4729518
  simp only [CollatzResearch.WordTrace]
  refine ⟨21562461609971437276531651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114999795253180998808168805 21562461609971437276531651)
  ·
    refine ⟨32343692414957155914797477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21562461609971437276531651 32343692414957155914797477)
    ·
      refine ⟨6064442327804466734024527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32343692414957155914797477 6064442327804466734024527)
      ·
        refine ⟨9096663491706700101036791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6064442327804466734024527 9096663491706700101036791)
        ·
          refine ⟨13644995237560050151555187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9096663491706700101036791 13644995237560050151555187)
          ·
            refine ⟨20467492856340075227332781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13644995237560050151555187 20467492856340075227332781)
            ·
              refine ⟨7675309821127528210249793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20467492856340075227332781 7675309821127528210249793)
              ·
                refine ⟨5756482365845646157687345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7675309821127528210249793 5756482365845646157687345)
                ·
                  refine ⟨4317361774384234618265509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5756482365845646157687345 4317361774384234618265509)
                  ·
                    refine ⟨809505332697043990924783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4317361774384234618265509 809505332697043990924783)
                    ·
                      rfl

theorem cell23_4729518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4729518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729518 prefixEnd_4729518 := by exact prefixLift 4729518
  have htrace : WordTrace (prefixWord ++ tailWord_4729518) baseStart_4729518 baseEnd_4729518 := by
    simpa [prefixWord, tailWord_4729518, baseEnd_4729518] using wordTrace_append hprefix tailTrace_4729518
  have hstable : (prefixWord ++ tailWord_4729518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729518).length < 2 ^ (prefixWord ++ tailWord_4729518).sum := by decide
  have hdescent : baseEnd_4729518 < baseStart_4729518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729525 : List Nat := [1, 3, 3, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_4729525 : Nat := 118140960795 + 4729525 * 2 ^ 59
def prefixEnd_4729525 : Nat := 4983230072969 + 3 ^ 40 * 4729525 * 2
def baseEnd_4729525 : Nat := 2428519592455713445386817

theorem tailTrace_4729525 : CollatzResearch.WordTrace tailWord_4729525 prefixEnd_4729525 2428519592455713445386817 := by
  unfold tailWord_4729525
  simp only [CollatzResearch.WordTrace]
  refine ⟨172499948190746138407758029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114999965460497425605172019 172499948190746138407758029)
  ·
    refine ⟨64687480571529801902909261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172499948190746138407758029 64687480571529801902909261)
    ·
      refine ⟨24257805214323675713590973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64687480571529801902909261 24257805214323675713590973)
      ·
        refine ⟨9096676955371378392596615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24257805214323675713590973 9096676955371378392596615)
        ·
          refine ⟨13645015433057067588894923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9096676955371378392596615 13645015433057067588894923)
          ·
            refine ⟨20467523149585601383342385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13645015433057067588894923 20467523149585601383342385)
            ·
              refine ⟨15350642362189201037506789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20467523149585601383342385 15350642362189201037506789)
              ·
                refine ⟨2878245442910475194532523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15350642362189201037506789 2878245442910475194532523)
                ·
                  refine ⟨4317368164365712791798785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878245442910475194532523 4317368164365712791798785)
                  ·
                    refine ⟨3238026123274284593849089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4317368164365712791798785 3238026123274284593849089)
                    ·
                      refine ⟨2428519592455713445386817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238026123274284593849089 2428519592455713445386817)
                      ·
                        rfl

theorem cell23_4729525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_4729525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729525 prefixEnd_4729525 := by exact prefixLift 4729525
  have htrace : WordTrace (prefixWord ++ tailWord_4729525) baseStart_4729525 baseEnd_4729525 := by
    simpa [prefixWord, tailWord_4729525, baseEnd_4729525] using wordTrace_append hprefix tailTrace_4729525
  have hstable : (prefixWord ++ tailWord_4729525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729525).length < 2 ^ (prefixWord ++ tailWord_4729525).sum := by decide
  have hdescent : baseEnd_4729525 < baseStart_4729525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729567 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_4729567 : Nat := 118140960795 + 4729567 * 2 ^ 59
def prefixEnd_4729567 : Nat := 4983230072969 + 3 ^ 40 * 4729567 * 2
def baseEnd_4729567 : Nat := 2428541158643202281061623

theorem tailTrace_4729567 : CollatzResearch.WordTrace tailWord_4729567 prefixEnd_4729567 2428541158643202281061623 := by
  unfold tailWord_4729567
  simp only [CollatzResearch.WordTrace]
  refine ⟨172501480056593979580786955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115000986704395986387191303 172501480056593979580786955)
  ·
    refine ⟨258752220084890969371180433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172501480056593979580786955 258752220084890969371180433)
    ·
      refine ⟨194064165063668227028385325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258752220084890969371180433 194064165063668227028385325)
      ·
        refine ⟨72774061898875585135644497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194064165063668227028385325 72774061898875585135644497)
        ·
          refine ⟨54580546424156688851733373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72774061898875585135644497 54580546424156688851733373)
          ·
            refine ⟨20467704909058758319400015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54580546424156688851733373 20467704909058758319400015)
            ·
              refine ⟨30701557363588137479100023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20467704909058758319400015 30701557363588137479100023)
              ·
                refine ⟨46052336045382206218650035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30701557363588137479100023 46052336045382206218650035)
                ·
                  refine ⟨69078504068073309327975053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46052336045382206218650035 69078504068073309327975053)
                  ·
                    refine ⟨25904439025527490997990645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69078504068073309327975053 25904439025527490997990645)
                    ·
                      refine ⟨2428541158643202281061623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25904439025527490997990645 2428541158643202281061623)
                      ·
                        rfl

theorem cell23_4729567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_4729567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729567 prefixEnd_4729567 := by exact prefixLift 4729567
  have htrace : WordTrace (prefixWord ++ tailWord_4729567) baseStart_4729567 baseEnd_4729567 := by
    simpa [prefixWord, tailWord_4729567, baseEnd_4729567] using wordTrace_append hprefix tailTrace_4729567
  have hstable : (prefixWord ++ tailWord_4729567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729567).length < 2 ^ (prefixWord ++ tailWord_4729567).sum := by decide
  have hdescent : baseEnd_4729567 < baseStart_4729567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729577 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_4729577 : Nat := 118140960795 + 4729577 * 2 ^ 59
def prefixEnd_4729577 : Nat := 4983230072969 + 3 ^ 40 * 4729577 * 2
def baseEnd_4729577 : Nat := 2428546293449747241936577

theorem tailTrace_4729577 : CollatzResearch.WordTrace tailWord_4729577 prefixEnd_4729577 2428546293449747241936577 := by
  unfold tailWord_4729577
  simp only [CollatzResearch.WordTrace]
  refine ⟨172501844786557751288650985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115001229857705167525767323 172501844786557751288650985)
  ·
    refine ⟨129376383589918313466488239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172501844786557751288650985 129376383589918313466488239)
    ·
      refine ⟨194064575384877470199732359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129376383589918313466488239 194064575384877470199732359)
      ·
        refine ⟨291096863077316205299598539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194064575384877470199732359 291096863077316205299598539)
        ·
          refine ⟨436645294615974307949397809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291096863077316205299598539 436645294615974307949397809)
          ·
            refine ⟨327483970961980730962048357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436645294615974307949397809 327483970961980730962048357)
            ·
              refine ⟨61403244555371387055384067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327483970961980730962048357 61403244555371387055384067)
              ·
                refine ⟨92104866833057080583076101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61403244555371387055384067 92104866833057080583076101)
                ·
                  refine ⟨17269662531198202609326769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92104866833057080583076101 17269662531198202609326769)
                  ·
                    refine ⟨12952246898398651956995077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17269662531198202609326769 12952246898398651956995077)
                    ·
                      refine ⟨2428546293449747241936577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12952246898398651956995077 2428546293449747241936577)
                      ·
                        rfl

theorem cell23_4729577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_4729577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729577 prefixEnd_4729577 := by exact prefixLift 4729577
  have htrace : WordTrace (prefixWord ++ tailWord_4729577) baseStart_4729577 baseEnd_4729577 := by
    simpa [prefixWord, tailWord_4729577, baseEnd_4729577] using wordTrace_append hprefix tailTrace_4729577
  have hstable : (prefixWord ++ tailWord_4729577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729577).length < 2 ^ (prefixWord ++ tailWord_4729577).sum := by decide
  have hdescent : baseEnd_4729577 < baseStart_4729577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729614 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_4729614 : Nat := 118140960795 + 4729614 * 2 ^ 59
def prefixEnd_4729614 : Nat := 4983230072969 + 3 ^ 40 * 4729614 * 2
def baseEnd_4729614 : Nat := 2428565292233963597173907

theorem tailTrace_4729614 : CollatzResearch.WordTrace tailWord_4729614 prefixEnd_4729614 2428565292233963597173907 := by
  unfold tailWord_4729614
  simp only [CollatzResearch.WordTrace]
  refine ⟨21562899285927963325968487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115002129524949137738498597 21562899285927963325968487)
  ·
    refine ⟨32344348928891944988952731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21562899285927963325968487 32344348928891944988952731)
    ·
      refine ⟨48516523393337917483429097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32344348928891944988952731 48516523393337917483429097)
      ·
        refine ⟨36387392545003438112571823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48516523393337917483429097 36387392545003438112571823)
        ·
          refine ⟨54581088817505157168857735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36387392545003438112571823 54581088817505157168857735)
          ·
            refine ⟨81871633226257735753286603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54581088817505157168857735 81871633226257735753286603)
            ·
              refine ⟨122807449839386603629929905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81871633226257735753286603 122807449839386603629929905)
              ·
                refine ⟨92105587379539952722447429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122807449839386603629929905 92105587379539952722447429)
                ·
                  refine ⟨17269797633663741135458893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92105587379539952722447429 17269797633663741135458893)
                  ·
                    refine ⟨6476174112623902925797085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17269797633663741135458893 6476174112623902925797085)
                    ·
                      refine ⟨2428565292233963597173907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6476174112623902925797085 2428565292233963597173907)
                      ·
                        rfl

theorem cell23_4729614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_4729614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729614 prefixEnd_4729614 := by exact prefixLift 4729614
  have htrace : WordTrace (prefixWord ++ tailWord_4729614) baseStart_4729614 baseEnd_4729614 := by
    simpa [prefixWord, tailWord_4729614, baseEnd_4729614] using wordTrace_append hprefix tailTrace_4729614
  have hstable : (prefixWord ++ tailWord_4729614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729614).length < 2 ^ (prefixWord ++ tailWord_4729614).sum := by decide
  have hdescent : baseEnd_4729614 < baseStart_4729614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729617 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 1, 7]
def baseStart_4729617 : Nat := 118140960795 + 4729617 * 2 ^ 59
def prefixEnd_4729617 : Nat := 4983230072969 + 3 ^ 40 * 4729617 * 2
def baseEnd_4729617 : Nat := 809522277558642361812131

theorem tailTrace_4729617 : CollatzResearch.WordTrace tailWord_4729617 prefixEnd_4729617 809522277558642361812131 := by
  unfold tailWord_4729617
  simp only [CollatzResearch.WordTrace]
  refine ⟨172503303706412838120107105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115002202470941892080071403 172503303706412838120107105)
  ·
    refine ⟨129377477779809628590080329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172503303706412838120107105 129377477779809628590080329)
    ·
      refine ⟨97033108334857221442560247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129377477779809628590080329 97033108334857221442560247)
      ·
        refine ⟨145549662502285832163840371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97033108334857221442560247 145549662502285832163840371)
        ·
          refine ⟨218324493753428748245760557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145549662502285832163840371 218324493753428748245760557)
          ·
            refine ⟨81871685157535780592160209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218324493753428748245760557 81871685157535780592160209)
            ·
              refine ⟨61403763868151835444120157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81871685157535780592160209 61403763868151835444120157)
              ·
                refine ⟨23026411450556938291545059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61403763868151835444120157 23026411450556938291545059)
                ·
                  refine ⟨34539617175835407437317589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23026411450556938291545059 34539617175835407437317589)
                  ·
                    refine ⟨809522277558642361812131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34539617175835407437317589 809522277558642361812131)
                    ·
                      rfl

theorem cell23_4729617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_4729617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729617 prefixEnd_4729617 := by exact prefixLift 4729617
  have htrace : WordTrace (prefixWord ++ tailWord_4729617) baseStart_4729617 baseEnd_4729617 := by
    simpa [prefixWord, tailWord_4729617, baseEnd_4729617] using wordTrace_append hprefix tailTrace_4729617
  have hstable : (prefixWord ++ tailWord_4729617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729617).length < 2 ^ (prefixWord ++ tailWord_4729617).sum := by decide
  have hdescent : baseEnd_4729617 < baseStart_4729617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729668 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4729668 : Nat := 118140960795 + 4729668 * 2 ^ 59
def prefixEnd_4729668 : Nat := 4983230072969 + 3 ^ 40 * 4729668 * 2
def baseEnd_4729668 : Nat := 809531006729768795299553

theorem tailTrace_4729668 : CollatzResearch.WordTrace tailWord_4729668 prefixEnd_4729668 809531006729768795299553 := by
  unfold tailWord_4729668
  simp only [CollatzResearch.WordTrace]
  refine ⟨86252581914614036915106829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115003442552818715886809105 86252581914614036915106829)
  ·
    refine ⟨32344718217980263843165061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86252581914614036915106829 32344718217980263843165061)
    ·
      refine ⟨6064634665871299470593449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32344718217980263843165061 6064634665871299470593449)
      ·
        refine ⟨4548475999403474602945087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6064634665871299470593449 4548475999403474602945087)
        ·
          refine ⟨6822713999105211904417631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4548475999403474602945087 6822713999105211904417631)
          ·
            refine ⟨10234070998657817856626447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6822713999105211904417631 10234070998657817856626447)
            ·
              refine ⟨15351106497986726784939671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10234070998657817856626447 15351106497986726784939671)
              ·
                refine ⟨23026659746980090177409507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15351106497986726784939671 23026659746980090177409507)
                ·
                  refine ⟨34539989620470135266114261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23026659746980090177409507 34539989620470135266114261)
                  ·
                    refine ⟨809531006729768795299553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34539989620470135266114261 809531006729768795299553)
                    ·
                      rfl

theorem cell23_4729668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4729668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729668 prefixEnd_4729668 := by exact prefixLift 4729668
  have htrace : WordTrace (prefixWord ++ tailWord_4729668) baseStart_4729668 baseEnd_4729668 := by
    simpa [prefixWord, tailWord_4729668, baseEnd_4729668] using wordTrace_append hprefix tailTrace_4729668
  have hstable : (prefixWord ++ tailWord_4729668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729668).length < 2 ^ (prefixWord ++ tailWord_4729668).sum := by decide
  have hdescent : baseEnd_4729668 < baseStart_4729668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729724 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_4729724 : Nat := 118140960795 + 4729724 * 2 ^ 59
def prefixEnd_4729724 : Nat := 4983230072969 + 3 ^ 40 * 4729724 * 2
def baseEnd_4729724 : Nat := 809540591701986055599467

theorem tailTrace_4729724 : CollatzResearch.WordTrace tailWord_4729724 prefixEnd_4729724 809540591701986055599467 := by
  unfold tailWord_4729724
  simp only [CollatzResearch.WordTrace]
  refine ⟨86253603158512597697126113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115004804211350130262834817 86253603158512597697126113)
  ·
    refine ⟨64690202368884448272844585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86253603158512597697126113 64690202368884448272844585)
    ·
      refine ⟨48517651776663336204633439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64690202368884448272844585 48517651776663336204633439)
      ·
        refine ⟨72776477664995004306950159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48517651776663336204633439 72776477664995004306950159)
        ·
          refine ⟨109164716497492506460425239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72776477664995004306950159 109164716497492506460425239)
          ·
            refine ⟨163747074746238759690637859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109164716497492506460425239 163747074746238759690637859)
            ·
              refine ⟨245620612119358139535956789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163747074746238759690637859 245620612119358139535956789)
              ·
                refine ⟨23026932386189825581495949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 245620612119358139535956789 23026932386189825581495949)
                ·
                  refine ⟨8635099644821184593060981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23026932386189825581495949 8635099644821184593060981)
                  ·
                    refine ⟨809540591701986055599467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8635099644821184593060981 809540591701986055599467)
                    ·
                      rfl

theorem cell23_4729724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_4729724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729724 prefixEnd_4729724 := by exact prefixLift 4729724
  have htrace : WordTrace (prefixWord ++ tailWord_4729724) baseStart_4729724 baseEnd_4729724 := by
    simpa [prefixWord, tailWord_4729724, baseEnd_4729724] using wordTrace_append hprefix tailTrace_4729724
  have hstable : (prefixWord ++ tailWord_4729724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729724).length < 2 ^ (prefixWord ++ tailWord_4729724).sum := by decide
  have hdescent : baseEnd_4729724 < baseStart_4729724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729731 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 1, 5, 2]
def baseStart_4729731 : Nat := 118140960795 + 4729731 * 2 ^ 59
def prefixEnd_4729731 : Nat := 4983230072969 + 3 ^ 40 * 4729731 * 2
def baseEnd_4729731 : Nat := 2428625369470539639410869

theorem tailTrace_4729731 : CollatzResearch.WordTrace tailWord_4729731 prefixEnd_4729731 2428625369470539639410869 := by
  unfold tailWord_4729731
  simp only [CollatzResearch.WordTrace]
  refine ⟨172507461627999835589757047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115004974418666557059838031 172507461627999835589757047)
  ·
    refine ⟨258761192441999753384635571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172507461627999835589757047 258761192441999753384635571)
    ·
      refine ⟨388141788662999630076953357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258761192441999753384635571 388141788662999630076953357)
      ·
        refine ⟨145553170748624861278857509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 388141788662999630076953357 145553170748624861278857509)
        ·
          refine ⟨27291219515367161489785783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145553170748624861278857509 27291219515367161489785783)
          ·
            refine ⟨40936829273050742234678675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27291219515367161489785783 40936829273050742234678675)
            ·
              refine ⟨61405243909576113352018013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40936829273050742234678675 61405243909576113352018013)
              ·
                refine ⟨23026966466091042507006755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61405243909576113352018013 23026966466091042507006755)
                ·
                  refine ⟨34540449699136563760510133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23026966466091042507006755 34540449699136563760510133)
                  ·
                    refine ⟨3238167159294052852547825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34540449699136563760510133 3238167159294052852547825)
                    ·
                      refine ⟨2428625369470539639410869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238167159294052852547825 2428625369470539639410869)
                      ·
                        rfl

theorem cell23_4729731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_4729731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729731 prefixEnd_4729731 := by exact prefixLift 4729731
  have htrace : WordTrace (prefixWord ++ tailWord_4729731) baseStart_4729731 baseEnd_4729731 := by
    simpa [prefixWord, tailWord_4729731, baseEnd_4729731] using wordTrace_append hprefix tailTrace_4729731
  have hstable : (prefixWord ++ tailWord_4729731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729731).length < 2 ^ (prefixWord ++ tailWord_4729731).sum := by decide
  have hdescent : baseEnd_4729731 < baseStart_4729731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729771 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 2, 4]
def baseStart_4729771 : Nat := 118140960795 + 4729771 * 2 ^ 59
def prefixEnd_4729771 : Nat := 4983230072969 + 3 ^ 40 * 4729771 * 2
def baseEnd_4729771 : Nat := 809548636232239827636895

theorem tailTrace_4729771 : CollatzResearch.WordTrace tailWord_4729771 prefixEnd_4729771 809548636232239827636895 := by
  unfold tailWord_4729771
  simp only [CollatzResearch.WordTrace]
  refine ⟨172508920547854922421213167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115005947031903281614142111 172508920547854922421213167)
  ·
    refine ⟨258763380821782383631819751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172508920547854922421213167 258763380821782383631819751)
    ·
      refine ⟨388145071232673575447729627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258763380821782383631819751 388145071232673575447729627)
      ·
        refine ⟨582217606849010363171594441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388145071232673575447729627 582217606849010363171594441)
        ·
          refine ⟨436663205136757772378695831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582217606849010363171594441 436663205136757772378695831)
          ·
            refine ⟨654994807705136658568043747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436663205136757772378695831 654994807705136658568043747)
            ·
              refine ⟨982492211557704987852065621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654994807705136658568043747 982492211557704987852065621)
              ·
                refine ⟨5756790302095927663195697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 982492211557704987852065621 5756790302095927663195697)
                ·
                  refine ⟨4317592726571945747396773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5756790302095927663195697 4317592726571945747396773)
                  ·
                    refine ⟨809548636232239827636895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4317592726571945747396773 809548636232239827636895)
                    ·
                      rfl

theorem cell23_4729771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 4].length) (baseStart_4729771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729771 prefixEnd_4729771 := by exact prefixLift 4729771
  have htrace : WordTrace (prefixWord ++ tailWord_4729771) baseStart_4729771 baseEnd_4729771 := by
    simpa [prefixWord, tailWord_4729771, baseEnd_4729771] using wordTrace_append hprefix tailTrace_4729771
  have hstable : (prefixWord ++ tailWord_4729771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729771).length < 2 ^ (prefixWord ++ tailWord_4729771).sum := by decide
  have hdescent : baseEnd_4729771 < baseStart_4729771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729784 : List Nat := [2, 1, 2, 1, 2, 4, 2, 9]
def baseStart_4729784 : Nat := 118140960795 + 4729784 * 2 ^ 59
def prefixEnd_4729784 : Nat := 4983230072969 + 3 ^ 40 * 4729784 * 2
def baseEnd_4729784 : Nat := 89950095701675108594375

theorem tailTrace_4729784 : CollatzResearch.WordTrace tailWord_4729784 prefixEnd_4729784 89950095701675108594375 := by
  unfold tailWord_4729784
  simp only [CollatzResearch.WordTrace]
  refine ⟨86254697348403912820718203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115006263131205217094290937 86254697348403912820718203)
  ·
    refine ⟨129382046022605869231077305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86254697348403912820718203 129382046022605869231077305)
    ·
      refine ⟨97036534516954401923307979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129382046022605869231077305 97036534516954401923307979)
      ·
        refine ⟨145554801775431602884961969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97036534516954401923307979 145554801775431602884961969)
        ·
          refine ⟨109166101331573702163721477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145554801775431602884961969 109166101331573702163721477)
          ·
            refine ⟨20468643999670069155697777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109166101331573702163721477 20468643999670069155697777)
            ·
              refine ⟨15351482999752551866773333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20468643999670069155697777 15351482999752551866773333)
              ·
                refine ⟨89950095701675108594375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15351482999752551866773333 89950095701675108594375)
                ·
                  rfl

theorem cell23_4729784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 9].length) (baseStart_4729784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729784 prefixEnd_4729784 := by exact prefixLift 4729784
  have htrace : WordTrace (prefixWord ++ tailWord_4729784) baseStart_4729784 baseEnd_4729784 := by
    simpa [prefixWord, tailWord_4729784, baseEnd_4729784] using wordTrace_append hprefix tailTrace_4729784
  have hstable : (prefixWord ++ tailWord_4729784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729784).length < 2 ^ (prefixWord ++ tailWord_4729784).sum := by decide
  have hdescent : baseEnd_4729784 < baseStart_4729784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729824 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_4729824 : Nat := 118140960795 + 4729824 * 2 ^ 59
def prefixEnd_4729824 : Nat := 4983230072969 + 3 ^ 40 * 4729824 * 2
def baseEnd_4729824 : Nat := 2428673123171407775547941

theorem tailTrace_4729824 : CollatzResearch.WordTrace tailWord_4729824 prefixEnd_4729824 2428673123171407775547941 := by
  unfold tailWord_4729824
  simp only [CollatzResearch.WordTrace]
  refine ⟨86255426808331456236446263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115007235744441941648595017 86255426808331456236446263)
  ·
    refine ⟨129383140212497184354669395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86255426808331456236446263 129383140212497184354669395)
    ·
      refine ⟨194074710318745776532004093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129383140212497184354669395 194074710318745776532004093)
      ·
        refine ⟨72778016369529666199501535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194074710318745776532004093 72778016369529666199501535)
        ·
          refine ⟨109167024554294499299252303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72778016369529666199501535 109167024554294499299252303)
          ·
            refine ⟨163750536831441748948878455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109167024554294499299252303 163750536831441748948878455)
            ·
              refine ⟨245625805247162623423317683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163750536831441748948878455 245625805247162623423317683)
              ·
                refine ⟨368438707870743935134976525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245625805247162623423317683 368438707870743935134976525)
                ·
                  refine ⟨138164515451528975675616197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368438707870743935134976525 138164515451528975675616197)
                  ·
                    refine ⟨25905846647161682939178037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138164515451528975675616197 25905846647161682939178037)
                    ·
                      refine ⟨2428673123171407775547941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25905846647161682939178037 2428673123171407775547941)
                      ·
                        rfl

theorem cell23_4729824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_4729824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729824 prefixEnd_4729824 := by exact prefixLift 4729824
  have htrace : WordTrace (prefixWord ++ tailWord_4729824) baseStart_4729824 baseEnd_4729824 := by
    simpa [prefixWord, tailWord_4729824, baseEnd_4729824] using wordTrace_append hprefix tailTrace_4729824
  have hstable : (prefixWord ++ tailWord_4729824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729824).length < 2 ^ (prefixWord ++ tailWord_4729824).sum := by decide
  have hdescent : baseEnd_4729824 < baseStart_4729824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729881 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_4729881 : Nat := 118140960795 + 4729881 * 2 ^ 59
def prefixEnd_4729881 : Nat := 4983230072969 + 3 ^ 40 * 4729881 * 2
def baseEnd_4729881 : Nat := 2428702391568714052535179

theorem tailTrace_4729881 : CollatzResearch.WordTrace tailWord_4729881 prefixEnd_4729881 2428702391568714052535179 := by
  unfold tailWord_4729881
  simp only [CollatzResearch.WordTrace]
  refine ⟨172512932577456411207717497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115008621718304274138478331 172512932577456411207717497)
  ·
    refine ⟨129384699433092308405788123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172512932577456411207717497 129384699433092308405788123)
    ·
      refine ⟨194077049149638462608682185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129384699433092308405788123 194077049149638462608682185)
      ·
        refine ⟨145557786862228846956511639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194077049149638462608682185 145557786862228846956511639)
        ·
          refine ⟨218336680293343270434767459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145557786862228846956511639 218336680293343270434767459)
          ·
            refine ⟨327505020440014905652151189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218336680293343270434767459 327505020440014905652151189)
            ·
              refine ⟨15351797833125698702444587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 327505020440014905652151189 15351797833125698702444587)
              ·
                refine ⟨23027696749688548053666881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15351797833125698702444587 23027696749688548053666881)
                ·
                  refine ⟨17270772562266411040250161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23027696749688548053666881 17270772562266411040250161)
                  ·
                    refine ⟨12953079421699808280187621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17270772562266411040250161 12953079421699808280187621)
                    ·
                      refine ⟨2428702391568714052535179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12953079421699808280187621 2428702391568714052535179)
                      ·
                        rfl

theorem cell23_4729881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_4729881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729881 prefixEnd_4729881 := by exact prefixLift 4729881
  have htrace : WordTrace (prefixWord ++ tailWord_4729881) baseStart_4729881 baseEnd_4729881 := by
    simpa [prefixWord, tailWord_4729881, baseEnd_4729881] using wordTrace_append hprefix tailTrace_4729881
  have hstable : (prefixWord ++ tailWord_4729881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729881).length < 2 ^ (prefixWord ++ tailWord_4729881).sum := by decide
  have hdescent : baseEnd_4729881 < baseStart_4729881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729891 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 7]
def baseStart_4729891 : Nat := 118140960795 + 4729891 * 2 ^ 59
def prefixEnd_4729891 : Nat := 4983230072969 + 3 ^ 40 * 4729891 * 2
def baseEnd_4729891 : Nat := 269856391819473223712237

theorem tailTrace_4729891 : CollatzResearch.WordTrace tailWord_4729891 prefixEnd_4729891 269856391819473223712237 := by
  unfold tailWord_4729891
  simp only [CollatzResearch.WordTrace]
  refine ⟨172513297307420182915581527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115008864871613455277054351 172513297307420182915581527)
  ·
    refine ⟨258769945961130274373372291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172513297307420182915581527 258769945961130274373372291)
    ·
      refine ⟨388154918941695411560058437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258769945961130274373372291 388154918941695411560058437)
      ·
        refine ⟨72779047301567889667510957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 388154918941695411560058437 72779047301567889667510957)
        ·
          refine ⟨27292142738087958625316609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72779047301567889667510957 27292142738087958625316609)
          ·
            refine ⟨20469107053565968968987457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27292142738087958625316609 20469107053565968968987457)
            ·
              refine ⟨15351830290174476726740593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20469107053565968968987457 15351830290174476726740593)
              ·
                refine ⟨11513872717630857545055445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15351830290174476726740593 11513872717630857545055445)
                ·
                  refine ⟨269856391819473223712237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11513872717630857545055445 269856391819473223712237)
                  ·
                    rfl

theorem cell23_4729891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 7].length) (baseStart_4729891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729891 prefixEnd_4729891 := by exact prefixLift 4729891
  have htrace : WordTrace (prefixWord ++ tailWord_4729891) baseStart_4729891 baseEnd_4729891 := by
    simpa [prefixWord, tailWord_4729891, baseEnd_4729891] using wordTrace_append hprefix tailTrace_4729891
  have hstable : (prefixWord ++ tailWord_4729891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729891).length < 2 ^ (prefixWord ++ tailWord_4729891).sum := by decide
  have hdescent : baseEnd_4729891 < baseStart_4729891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729928 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 2, 5, 2]
def baseStart_4729928 : Nat := 118140960795 + 4729928 * 2 ^ 59
def prefixEnd_4729928 : Nat := 4983230072969 + 3 ^ 40 * 4729928 * 2
def baseEnd_4729928 : Nat := 2428726525159475368647463

theorem tailTrace_4729928 : CollatzResearch.WordTrace tailWord_4729928 prefixEnd_4729928 2428726525159475368647463 := by
  unfold tailWord_4729928
  simp only [CollatzResearch.WordTrace]
  refine ⟨86257323404143069117339219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115009764538857425489785625 86257323404143069117339219)
  ·
    refine ⟨129385985106214603676008829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86257323404143069117339219 129385985106214603676008829)
    ·
      refine ⟨48519744414830476378503311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129385985106214603676008829 48519744414830476378503311)
      ·
        refine ⟨72779616622245714567754967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48519744414830476378503311 72779616622245714567754967)
        ·
          refine ⟨109169424933368571851632451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72779616622245714567754967 109169424933368571851632451)
          ·
            refine ⟨163754137400052857777448677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109169424933368571851632451 163754137400052857777448677)
            ·
              refine ⟨30703900762509910833271627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163754137400052857777448677 30703900762509910833271627)
              ·
                refine ⟨46055851143764866249907441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30703900762509910833271627 46055851143764866249907441)
                ·
                  refine ⟨34541888357823649687430581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46055851143764866249907441 34541888357823649687430581)
                  ·
                    refine ⟨3238302033545967158196617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34541888357823649687430581 3238302033545967158196617)
                    ·
                      refine ⟨2428726525159475368647463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238302033545967158196617 2428726525159475368647463)
                      ·
                        rfl

theorem cell23_4729928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 5, 2].length) (baseStart_4729928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729928 prefixEnd_4729928 := by exact prefixLift 4729928
  have htrace : WordTrace (prefixWord ++ tailWord_4729928) baseStart_4729928 baseEnd_4729928 := by
    simpa [prefixWord, tailWord_4729928, baseEnd_4729928] using wordTrace_append hprefix tailTrace_4729928
  have hstable : (prefixWord ++ tailWord_4729928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729928).length < 2 ^ (prefixWord ++ tailWord_4729928).sum := by decide
  have hdescent : baseEnd_4729928 < baseStart_4729928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4729992 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4729992 : Nat := 118140960795 + 4729992 * 2 ^ 59
def prefixEnd_4729992 : Nat := 4983230072969 + 3 ^ 40 * 4729992 * 2
def baseEnd_4729992 : Nat := 2428759387921363118247169

theorem tailTrace_4729992 : CollatzResearch.WordTrace tailWord_4729992 prefixEnd_4729992 2428759387921363118247169 := by
  unfold tailWord_4729992
  simp only [CollatzResearch.WordTrace]
  refine ⟨86258490540027138582504115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115011320720036184776672153 86258490540027138582504115)
  ·
    refine ⟨129387735810040707873756173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86258490540027138582504115 129387735810040707873756173)
    ·
      refine ⟨48520400928765265452658565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129387735810040707873756173 48520400928765265452658565)
      ·
        refine ⟨9097575174143487272373481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48520400928765265452658565 9097575174143487272373481)
        ·
          refine ⟨6823181380607615454280111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9097575174143487272373481 6823181380607615454280111)
          ·
            refine ⟨10234772070911423181420167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823181380607615454280111 10234772070911423181420167)
            ·
              refine ⟨15352158106367134772130251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10234772070911423181420167 15352158106367134772130251)
              ·
                refine ⟨23028237159550702158195377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15352158106367134772130251 23028237159550702158195377)
                ·
                  refine ⟨17271177869663026618646533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23028237159550702158195377 17271177869663026618646533)
                  ·
                    refine ⟨3238345850561817490996225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17271177869663026618646533 3238345850561817490996225)
                    ·
                      refine ⟨2428759387921363118247169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238345850561817490996225 2428759387921363118247169)
                      ·
                        rfl

theorem cell23_4729992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4729992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4729992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4729992 prefixEnd_4729992 := by exact prefixLift 4729992
  have htrace : WordTrace (prefixWord ++ tailWord_4729992) baseStart_4729992 baseEnd_4729992 := by
    simpa [prefixWord, tailWord_4729992, baseEnd_4729992] using wordTrace_append hprefix tailTrace_4729992
  have hstable : (prefixWord ++ tailWord_4729992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4729992).length < 2 ^ (prefixWord ++ tailWord_4729992).sum := by decide
  have hdescent : baseEnd_4729992 < baseStart_4729992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4729992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730012 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_4730012 : Nat := 118140960795 + 4730012 * 2 ^ 59
def prefixEnd_4730012 : Nat := 4983230072969 + 3 ^ 40 * 4730012 * 2
def baseEnd_4730012 : Nat := 2428769657534453039997077

theorem tailTrace_4730012 : CollatzResearch.WordTrace tailWord_4730012 prefixEnd_4730012 2428769657534453039997077 := by
  unfold tailWord_4730012
  simp only [CollatzResearch.WordTrace]
  refine ⟨86258855269990910290368145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115011807026654547053824193 86258855269990910290368145)
  ·
    refine ⟨64694141452493182717776109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86258855269990910290368145 64694141452493182717776109)
    ·
      refine ⟨24260303044684943519166041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64694141452493182717776109 24260303044684943519166041)
      ·
        refine ⟨18195227283513707639374531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24260303044684943519166041 18195227283513707639374531)
        ·
          refine ⟨27292840925270561459061797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18195227283513707639374531 27292840925270561459061797)
          ·
            refine ⟨5117407673488230273574087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27292840925270561459061797 5117407673488230273574087)
            ·
              refine ⟨7676111510232345410361131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117407673488230273574087 7676111510232345410361131)
              ·
                refine ⟨11514167265348518115541697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7676111510232345410361131 11514167265348518115541697)
                ·
                  refine ⟨8635625449011388586656273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11514167265348518115541697 8635625449011388586656273)
                  ·
                    refine ⟨6476719086758541439992205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8635625449011388586656273 6476719086758541439992205)
                    ·
                      refine ⟨2428769657534453039997077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6476719086758541439992205 2428769657534453039997077)
                      ·
                        rfl

theorem cell23_4730012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_4730012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730012 prefixEnd_4730012 := by exact prefixLift 4730012
  have htrace : WordTrace (prefixWord ++ tailWord_4730012) baseStart_4730012 baseEnd_4730012 := by
    simpa [prefixWord, tailWord_4730012, baseEnd_4730012] using wordTrace_append hprefix tailTrace_4730012
  have hstable : (prefixWord ++ tailWord_4730012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730012).length < 2 ^ (prefixWord ++ tailWord_4730012).sum := by decide
  have hdescent : baseEnd_4730012 < baseStart_4730012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730035 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 2, 3, 2]
def baseStart_4730035 : Nat := 118140960795 + 4730035 * 2 ^ 59
def prefixEnd_4730035 : Nat := 4983230072969 + 3 ^ 40 * 4730035 * 2
def baseEnd_4730035 : Nat := 2428781467589506450009471

theorem tailTrace_4730035 : CollatzResearch.WordTrace tailWord_4730035 prefixEnd_4730035 2428781467589506450009471 := by
  unfold tailWord_4730035
  simp only [CollatzResearch.WordTrace]
  refine ⟨172518549418898495508823559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115012366279265663672549039 172518549418898495508823559)
  ·
    refine ⟨258777824128347743263235339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172518549418898495508823559 258777824128347743263235339)
    ·
      refine ⟨388166736192521614894853009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258777824128347743263235339 388166736192521614894853009)
      ·
        refine ⟨291125052144391211171139757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388166736192521614894853009 291125052144391211171139757)
        ·
          refine ⟨109171894554146704189177409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291125052144391211171139757 109171894554146704189177409)
          ·
            refine ⟨81878920915610028141883057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109171894554146704189177409 81878920915610028141883057)
            ·
              refine ⟨61409190686707521106412293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81878920915610028141883057 61409190686707521106412293)
              ·
                refine ⟨11514223253757660207452305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61409190686707521106412293 11514223253757660207452305)
                ·
                  refine ⟨8635667440318245155589229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11514223253757660207452305 8635667440318245155589229)
                  ·
                    refine ⟨3238375290119341933345961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8635667440318245155589229 3238375290119341933345961)
                    ·
                      refine ⟨2428781467589506450009471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238375290119341933345961 2428781467589506450009471)
                      ·
                        rfl

theorem cell23_4730035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 3, 2].length) (baseStart_4730035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730035 prefixEnd_4730035 := by exact prefixLift 4730035
  have htrace : WordTrace (prefixWord ++ tailWord_4730035) baseStart_4730035 baseEnd_4730035 := by
    simpa [prefixWord, tailWord_4730035, baseEnd_4730035] using wordTrace_append hprefix tailTrace_4730035
  have hstable : (prefixWord ++ tailWord_4730035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730035).length < 2 ^ (prefixWord ++ tailWord_4730035).sum := by decide
  have hdescent : baseEnd_4730035 < baseStart_4730035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730062 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_4730062 : Nat := 118140960795 + 4730062 * 2 ^ 59
def prefixEnd_4730062 : Nat := 4983230072969 + 3 ^ 40 * 4730062 * 2
def baseEnd_4730062 : Nat := 809598443855725948123949

theorem tailTrace_4730062 : CollatzResearch.WordTrace tailWord_4730062 prefixEnd_4730062 809598443855725948123949 := by
  unfold tailWord_4730062
  simp only [CollatzResearch.WordTrace]
  refine ⟨21564941773725084890007055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115013022793200452746704293 21564941773725084890007055)
  ·
    refine ⟨32347412660587627335010583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21564941773725084890007055 32347412660587627335010583)
    ·
      refine ⟨48521118990881441002515875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32347412660587627335010583 48521118990881441002515875)
      ·
        refine ⟨72781678486322161503773813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48521118990881441002515875 72781678486322161503773813)
        ·
          refine ⟨6823282358092702640978795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72781678486322161503773813 6823282358092702640978795)
          ·
            refine ⟨10234923537139053961468193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823282358092702640978795 10234923537139053961468193)
            ·
              refine ⟨7676192652854290471101145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10234923537139053961468193 7676192652854290471101145)
              ·
                refine ⟨5757144489640717853325859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7676192652854290471101145 5757144489640717853325859)
                ·
                  refine ⟨8635716734461076779988789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5757144489640717853325859 8635716734461076779988789)
                  ·
                    refine ⟨809598443855725948123949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8635716734461076779988789 809598443855725948123949)
                    ·
                      rfl

theorem cell23_4730062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_4730062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730062 prefixEnd_4730062 := by exact prefixLift 4730062
  have htrace : WordTrace (prefixWord ++ tailWord_4730062) baseStart_4730062 baseEnd_4730062 := by
    simpa [prefixWord, tailWord_4730062, baseEnd_4730062] using wordTrace_append hprefix tailTrace_4730062
  have hstable : (prefixWord ++ tailWord_4730062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730062).length < 2 ^ (prefixWord ++ tailWord_4730062).sum := by decide
  have hdescent : baseEnd_4730062 < baseStart_4730062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730099 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 3, 2, 2]
def baseStart_4730099 : Nat := 118140960795 + 4730099 * 2 ^ 59
def prefixEnd_4730099 : Nat := 4983230072969 + 3 ^ 40 * 4730099 * 2
def baseEnd_4730099 : Nat := 2428814330351394199609177

theorem tailTrace_4730099 : CollatzResearch.WordTrace tailWord_4730099 prefixEnd_4730099 2428814330351394199609177 := by
  unfold tailWord_4730099
  simp only [CollatzResearch.WordTrace]
  refine ⟨172520883690666634439153351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115013922460444422959435567 172520883690666634439153351)
  ·
    refine ⟨258781325535999951658730027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172520883690666634439153351 258781325535999951658730027)
    ·
      refine ⟨388171988303999927488095041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258781325535999951658730027 388171988303999927488095041)
      ·
        refine ⟨291128991227999945616071281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388171988303999927488095041 291128991227999945616071281)
        ·
          refine ⟨218346743420999959212053461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291128991227999945616071281 218346743420999959212053461)
          ·
            refine ⟨5117501798929686544032503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 218346743420999959212053461 5117501798929686544032503)
            ·
              refine ⟨7676252698394529816048755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117501798929686544032503 7676252698394529816048755)
              ·
                refine ⟨11514379047591794724073133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7676252698394529816048755 11514379047591794724073133)
                ·
                  refine ⟨4317892142846923021527425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11514379047591794724073133 4317892142846923021527425)
                  ·
                    refine ⟨3238419107135192266145569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4317892142846923021527425 3238419107135192266145569)
                    ·
                      refine ⟨2428814330351394199609177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238419107135192266145569 2428814330351394199609177)
                      ·
                        rfl

theorem cell23_4730099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 2, 2].length) (baseStart_4730099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730099 prefixEnd_4730099 := by exact prefixLift 4730099
  have htrace : WordTrace (prefixWord ++ tailWord_4730099) baseStart_4730099 baseEnd_4730099 := by
    simpa [prefixWord, tailWord_4730099, baseEnd_4730099] using wordTrace_append hprefix tailTrace_4730099
  have hstable : (prefixWord ++ tailWord_4730099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730099).length < 2 ^ (prefixWord ++ tailWord_4730099).sum := by decide
  have hdescent : baseEnd_4730099 < baseStart_4730099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730149 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 3]
def baseStart_4730149 : Nat := 118140960795 + 4730149 * 2 ^ 59
def prefixEnd_4730149 : Nat := 4983230072969 + 3 ^ 40 * 4730149 * 2
def baseEnd_4730149 : Nat := 2428840004384119003983947

theorem tailTrace_4730149 : CollatzResearch.WordTrace tailWord_4730149 prefixEnd_4730149 2428840004384119003983947 := by
  unfold tailWord_4730149
  simp only [CollatzResearch.WordTrace]
  refine ⟨172522707340485492978473501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115015138226990328652315667 172522707340485492978473501)
  ·
    refine ⟨64696015252682059866927563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172522707340485492978473501 64696015252682059866927563)
    ·
      refine ⟨97044022879023089800391345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64696015252682059866927563 97044022879023089800391345)
      ·
        refine ⟨72783017159267317350293509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97044022879023089800391345 72783017159267317350293509)
        ·
          refine ⟨13646815717362622003180033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72783017159267317350293509 13646815717362622003180033)
          ·
            refine ⟨10235111788021966502385025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13646815717362622003180033 10235111788021966502385025)
            ·
              refine ⟨7676333841016474876788769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10235111788021966502385025 7676333841016474876788769)
              ·
                refine ⟨5757250380762356157591577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7676333841016474876788769 5757250380762356157591577)
                ·
                  refine ⟨4317937785571767118193683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5757250380762356157591577 4317937785571767118193683)
                  ·
                    refine ⟨6476906678357650677290525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4317937785571767118193683 6476906678357650677290525)
                    ·
                      refine ⟨2428840004384119003983947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6476906678357650677290525 2428840004384119003983947)
                      ·
                        rfl

theorem cell23_4730149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_4730149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730149 prefixEnd_4730149 := by exact prefixLift 4730149
  have htrace : WordTrace (prefixWord ++ tailWord_4730149) baseStart_4730149 baseEnd_4730149 := by
    simpa [prefixWord, tailWord_4730149, baseEnd_4730149] using wordTrace_append hprefix tailTrace_4730149
  have hstable : (prefixWord ++ tailWord_4730149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730149).length < 2 ^ (prefixWord ++ tailWord_4730149).sum := by decide
  have hdescent : baseEnd_4730149 < baseStart_4730149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730165 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_4730165 : Nat := 118140960795 + 4730165 * 2 ^ 59
def prefixEnd_4730165 : Nat := 4983230072969 + 3 ^ 40 * 4730165 * 2
def baseEnd_4730165 : Nat := 809616073358196980461291

theorem tailTrace_4730165 : CollatzResearch.WordTrace tailWord_4730165 prefixEnd_4730165 809616073358196980461291 := by
  unfold tailWord_4730165
  simp only [CollatzResearch.WordTrace]
  refine ⟨172523290908427527711055949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115015527272285018474037299 172523290908427527711055949)
  ·
    refine ⟨64696234090660322891645981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172523290908427527711055949 64696234090660322891645981)
    ·
      refine ⟨24261087783997621084367243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64696234090660322891645981 24261087783997621084367243)
      ·
        refine ⟨36391631675996431626550865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24261087783997621084367243 36391631675996431626550865)
        ·
          refine ⟨27293723756997323719913149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36391631675996431626550865 27293723756997323719913149)
          ·
            refine ⟨10235146408873996394967431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27293723756997323719913149 10235146408873996394967431)
            ·
              refine ⟨15352719613310994592451147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10235146408873996394967431 15352719613310994592451147)
              ·
                refine ⟨23029079419966491888676721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15352719613310994592451147 23029079419966491888676721)
                ·
                  refine ⟨17271809564974868916507541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23029079419966491888676721 17271809564974868916507541)
                  ·
                    refine ⟨809616073358196980461291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17271809564974868916507541 809616073358196980461291)
                    ·
                      rfl

theorem cell23_4730165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_4730165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730165 prefixEnd_4730165 := by exact prefixLift 4730165
  have htrace : WordTrace (prefixWord ++ tailWord_4730165) baseStart_4730165 baseEnd_4730165 := by
    simpa [prefixWord, tailWord_4730165, baseEnd_4730165] using wordTrace_append hprefix tailTrace_4730165
  have hstable : (prefixWord ++ tailWord_4730165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730165).length < 2 ^ (prefixWord ++ tailWord_4730165).sum := by decide
  have hdescent : baseEnd_4730165 < baseStart_4730165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730166 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4730166 : Nat := 118140960795 + 4730166 * 2 ^ 59
def prefixEnd_4730166 : Nat := 4983230072969 + 3 ^ 40 * 4730166 * 2
def baseEnd_4730166 : Nat := 2428848733555245437471369

theorem tailTrace_4730166 : CollatzResearch.WordTrace tailWord_4730166 prefixEnd_4730166 2428848733555245437471369 := by
  unfold tailWord_4730166
  simp only [CollatzResearch.WordTrace]
  refine ⟨10782707961338994055115147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115015551587615936587894901 10782707961338994055115147)
  ·
    refine ⟨16174061942008491082672721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10782707961338994055115147 16174061942008491082672721)
    ·
      refine ⟨12130546456506368312004541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16174061942008491082672721 12130546456506368312004541)
      ·
        refine ⟨4548954921189888117001703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12130546456506368312004541 4548954921189888117001703)
        ·
          refine ⟨6823432381784832175502555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4548954921189888117001703 6823432381784832175502555)
          ·
            refine ⟨10235148572677248263253833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823432381784832175502555 10235148572677248263253833)
            ·
              refine ⟨7676361429507936197440375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10235148572677248263253833 7676361429507936197440375)
              ·
                refine ⟨11514542144261904296160563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7676361429507936197440375 11514542144261904296160563)
                ·
                  refine ⟨17271813216392856444240845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11514542144261904296160563 17271813216392856444240845)
                  ·
                    refine ⟨6476929956147321166590317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17271813216392856444240845 6476929956147321166590317)
                    ·
                      refine ⟨2428848733555245437471369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6476929956147321166590317 2428848733555245437471369)
                      ·
                        rfl

theorem cell23_4730166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4730166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730166 prefixEnd_4730166 := by exact prefixLift 4730166
  have htrace : WordTrace (prefixWord ++ tailWord_4730166) baseStart_4730166 baseEnd_4730166 := by
    simpa [prefixWord, tailWord_4730166, baseEnd_4730166] using wordTrace_append hprefix tailTrace_4730166
  have hstable : (prefixWord ++ tailWord_4730166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730166).length < 2 ^ (prefixWord ++ tailWord_4730166).sum := by decide
  have hdescent : baseEnd_4730166 < baseStart_4730166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730172 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 1, 4, 2]
def baseStart_4730172 : Nat := 118140960795 + 4730172 * 2 ^ 59
def prefixEnd_4730172 : Nat := 4983230072969 + 3 ^ 40 * 4730172 * 2
def baseEnd_4730172 : Nat := 2428851814439172413996341

theorem tailTrace_4730172 : CollatzResearch.WordTrace tailWord_4730172 prefixEnd_4730172 2428851814439172413996341 := by
  unfold tailWord_4730172
  simp only [CollatzResearch.WordTrace]
  refine ⟨86261773109701083953280385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115015697479601445271040513 86261773109701083953280385)
  ·
    refine ⟨64696329832275812964960289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86261773109701083953280385 64696329832275812964960289)
    ·
      refine ⟨48522247374206859723720217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64696329832275812964960289 48522247374206859723720217)
      ·
        refine ⟨36391685530655144792790163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48522247374206859723720217 36391685530655144792790163)
        ·
          refine ⟨54587528295982717189185245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36391685530655144792790163 54587528295982717189185245)
          ·
            refine ⟨20470323110993518945944467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54587528295982717189185245 20470323110993518945944467)
            ·
              refine ⟨30705484666490278418916701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20470323110993518945944467 30705484666490278418916701)
              ·
                refine ⟨11514556749933854407093763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30705484666490278418916701 11514556749933854407093763)
                ·
                  refine ⟨17271835124900781610640645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11514556749933854407093763 17271835124900781610640645)
                  ·
                    refine ⟨3238469085918896551995121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17271835124900781610640645 3238469085918896551995121)
                    ·
                      refine ⟨2428851814439172413996341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238469085918896551995121 2428851814439172413996341)
                      ·
                        rfl

theorem cell23_4730172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_4730172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730172 prefixEnd_4730172 := by exact prefixLift 4730172
  have htrace : WordTrace (prefixWord ++ tailWord_4730172) baseStart_4730172 baseEnd_4730172 := by
    simpa [prefixWord, tailWord_4730172, baseEnd_4730172] using wordTrace_append hprefix tailTrace_4730172
  have hstable : (prefixWord ++ tailWord_4730172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730172).length < 2 ^ (prefixWord ++ tailWord_4730172).sum := by decide
  have hdescent : baseEnd_4730172 < baseStart_4730172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730212 : List Nat := [2, 3, 1, 1, 3, 2, 2, 4, 5]
def baseStart_4730212 : Nat := 118140960795 + 4730212 * 2 ^ 59
def prefixEnd_4730212 : Nat := 4983230072969 + 3 ^ 40 * 4730212 * 2
def baseEnd_4730212 : Nat := 269874705962816917499573

theorem tailTrace_4730212 : CollatzResearch.WordTrace tailWord_4730212 prefixEnd_4730212 269874705962816917499573 := by
  unfold tailWord_4730212
  simp only [CollatzResearch.WordTrace]
  refine ⟨86262502569628627369008445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115016670092838169825344593 86262502569628627369008445)
  ·
    refine ⟨32348438463610735263378167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86262502569628627369008445 32348438463610735263378167)
    ·
      refine ⟨48522657695416102895067251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32348438463610735263378167 48522657695416102895067251)
      ·
        refine ⟨72783986543124154342600877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48522657695416102895067251 72783986543124154342600877)
        ·
          refine ⟨27293994953671557878475329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72783986543124154342600877 27293994953671557878475329)
          ·
            refine ⟨20470496215253668408856497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27293994953671557878475329 20470496215253668408856497)
            ·
              refine ⟨15352872161440251306642373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20470496215253668408856497 15352872161440251306642373)
              ·
                refine ⟨2878663530270047119995445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15352872161440251306642373 2878663530270047119995445)
                ·
                  refine ⟨269874705962816917499573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2878663530270047119995445 269874705962816917499573)
                  ·
                    rfl

theorem cell23_4730212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_4730212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730212 prefixEnd_4730212 := by exact prefixLift 4730212
  have htrace : WordTrace (prefixWord ++ tailWord_4730212) baseStart_4730212 baseEnd_4730212 := by
    simpa [prefixWord, tailWord_4730212, baseEnd_4730212] using wordTrace_append hprefix tailTrace_4730212
  have hstable : (prefixWord ++ tailWord_4730212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730212).length < 2 ^ (prefixWord ++ tailWord_4730212).sum := by decide
  have hdescent : baseEnd_4730212 < baseStart_4730212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730245 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_4730245 : Nat := 118140960795 + 4730245 * 2 ^ 59
def prefixEnd_4730245 : Nat := 4983230072969 + 3 ^ 40 * 4730245 * 2
def baseEnd_4730245 : Nat := 2428889298526950628383505

theorem tailTrace_4730245 : CollatzResearch.WordTrace tailWord_4730245 prefixEnd_4730245 2428889298526950628383505 := by
  unfold tailWord_4730245
  simp only [CollatzResearch.WordTrace]
  refine ⟨172526208748137701373968189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115017472498758467582645459 172526208748137701373968189)
  ·
    refine ⟨64697328280551638015238071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172526208748137701373968189 64697328280551638015238071)
    ·
      refine ⟨97045992420827457022857107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64697328280551638015238071 97045992420827457022857107)
      ·
        refine ⟨145568988631241185534285661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97045992420827457022857107 145568988631241185534285661)
        ·
          refine ⟨54588370736715444575357123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145568988631241185534285661 54588370736715444575357123)
          ·
            refine ⟨81882556105073166863035685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54588370736715444575357123 81882556105073166863035685)
            ·
              refine ⟨15352979269701218786819191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81882556105073166863035685 15352979269701218786819191)
              ·
                refine ⟨23029468904551828180228787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15352979269701218786819191 23029468904551828180228787)
                ·
                  refine ⟨34544203356827742270343181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23029468904551828180228787 34544203356827742270343181)
                  ·
                    refine ⟨12954076258810403351378693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34544203356827742270343181 12954076258810403351378693)
                    ·
                      refine ⟨2428889298526950628383505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12954076258810403351378693 2428889298526950628383505)
                      ·
                        rfl

theorem cell23_4730245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_4730245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730245 prefixEnd_4730245 := by exact prefixLift 4730245
  have htrace : WordTrace (prefixWord ++ tailWord_4730245) baseStart_4730245 baseEnd_4730245 := by
    simpa [prefixWord, tailWord_4730245, baseEnd_4730245] using wordTrace_append hprefix tailTrace_4730245
  have hstable : (prefixWord ++ tailWord_4730245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730245).length < 2 ^ (prefixWord ++ tailWord_4730245).sum := by decide
  have hdescent : baseEnd_4730245 < baseStart_4730245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730346 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_4730346 : Nat := 118140960795 + 4730346 * 2 ^ 59
def prefixEnd_4730346 : Nat := 4983230072969 + 3 ^ 40 * 4730346 * 2
def baseEnd_4730346 : Nat := 2428941160073054733220541

theorem tailTrace_4730346 : CollatzResearch.WordTrace tailWord_4730346 prefixEnd_4730346 2428941160073054733220541 := by
  unfold tailWord_4730346
  simp only [CollatzResearch.WordTrace]
  refine ⟨43132473130192948905848723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115019928347181197082263261 43132473130192948905848723)
  ·
    refine ⟨64698709695289423358773085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43132473130192948905848723 64698709695289423358773085)
    ·
      refine ⟨24262016135733533759539907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64698709695289423358773085 24262016135733533759539907)
      ·
        refine ⟨36393024203600300639309861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24262016135733533759539907 36393024203600300639309861)
        ·
          refine ⟨6823692038175056369870599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36393024203600300639309861 6823692038175056369870599)
          ·
            refine ⟨10235538057262584554805899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823692038175056369870599 10235538057262584554805899)
            ·
              refine ⟨15353307085893876832208849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10235538057262584554805899 15353307085893876832208849)
              ·
                refine ⟨11514980314420407624156637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15353307085893876832208849 11514980314420407624156637)
                ·
                  refine ⟨4318117617907652859058739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11514980314420407624156637 4318117617907652859058739)
                  ·
                    refine ⟨6477176426861479288588109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4318117617907652859058739 6477176426861479288588109)
                    ·
                      refine ⟨2428941160073054733220541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6477176426861479288588109 2428941160073054733220541)
                      ·
                        rfl

theorem cell23_4730346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_4730346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730346 prefixEnd_4730346 := by exact prefixLift 4730346
  have htrace : WordTrace (prefixWord ++ tailWord_4730346) baseStart_4730346 baseEnd_4730346 := by
    simpa [prefixWord, tailWord_4730346, baseEnd_4730346] using wordTrace_append hprefix tailTrace_4730346
  have hstable : (prefixWord ++ tailWord_4730346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730346).length < 2 ^ (prefixWord ++ tailWord_4730346).sum := by decide
  have hdescent : baseEnd_4730346 < baseStart_4730346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730352 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_4730352 : Nat := 118140960795 + 4730352 * 2 ^ 59
def prefixEnd_4730352 : Nat := 4983230072969 + 3 ^ 40 * 4730352 * 2
def baseEnd_4730352 : Nat := 2428944240956981709745513

theorem tailTrace_4730352 : CollatzResearch.WordTrace tailWord_4730352 prefixEnd_4730352 2428944240956981709745513 := by
  unfold tailWord_4730352
  simp only [CollatzResearch.WordTrace]
  refine ⟨86265055679375029324056655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115020074239166705765408873 86265055679375029324056655)
  ·
    refine ⟨129397583519062543986084983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86265055679375029324056655 129397583519062543986084983)
    ·
      refine ⟨194096375278593815979127475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129397583519062543986084983 194096375278593815979127475)
      ·
        refine ⟨291144562917890723968691213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194096375278593815979127475 291144562917890723968691213)
        ·
          refine ⟨109179211094209021488259205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291144562917890723968691213 109179211094209021488259205)
          ·
            refine ⟨20471102080164191529048601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109179211094209021488259205 20471102080164191529048601)
            ·
              refine ⟨15353326560123143646786451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20471102080164191529048601 15353326560123143646786451)
              ·
                refine ⟨23029989840184715470179677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15353326560123143646786451 23029989840184715470179677)
                ·
                  refine ⟨8636246190069268301317379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23029989840184715470179677 8636246190069268301317379)
                  ·
                    refine ⟨12954369285103902451976069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8636246190069268301317379 12954369285103902451976069)
                    ·
                      refine ⟨2428944240956981709745513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12954369285103902451976069 2428944240956981709745513)
                      ·
                        rfl

theorem cell23_4730352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_4730352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730352 prefixEnd_4730352 := by exact prefixLift 4730352
  have htrace : WordTrace (prefixWord ++ tailWord_4730352) baseStart_4730352 baseEnd_4730352 := by
    simpa [prefixWord, tailWord_4730352, baseEnd_4730352] using wordTrace_append hprefix tailTrace_4730352
  have hstable : (prefixWord ++ tailWord_4730352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730352).length < 2 ^ (prefixWord ++ tailWord_4730352).sum := by decide
  have hdescent : baseEnd_4730352 < baseStart_4730352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730355 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 5]
def baseStart_4730355 : Nat := 118140960795 + 4730355 * 2 ^ 59
def prefixEnd_4730355 : Nat := 4983230072969 + 3 ^ 40 * 4730355 * 2
def baseEnd_4730355 : Nat := 2428945781398945198007999

theorem tailTrace_4730355 : CollatzResearch.WordTrace tailWord_4730355 prefixEnd_4730355 2428945781398945198007999 := by
  unfold tailWord_4730355
  simp only [CollatzResearch.WordTrace]
  refine ⟨172530220777739190160472519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115020147185159460106981679 172530220777739190160472519)
  ·
    refine ⟨258795331166608785240708779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172530220777739190160472519 258795331166608785240708779)
    ·
      refine ⟨388192996749913177861063169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258795331166608785240708779 388192996749913177861063169)
      ·
        refine ⟨291144747562434883395797377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388192996749913177861063169 291144747562434883395797377)
        ·
          refine ⟨218358560671826162546848033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291144747562434883395797377 218358560671826162546848033)
          ·
            refine ⟨163768920503869621910136025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218358560671826162546848033 163768920503869621910136025)
            ·
              refine ⟨122826690377902216432602019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163768920503869621910136025 122826690377902216432602019)
              ·
                refine ⟨184240035566853324648903029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122826690377902216432602019 184240035566853324648903029)
                ·
                  refine ⟨17272503334392499185834659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 184240035566853324648903029 17272503334392499185834659)
                  ·
                    refine ⟨25908755001588748778751989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17272503334392499185834659 25908755001588748778751989)
                    ·
                      refine ⟨2428945781398945198007999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25908755001588748778751989 2428945781398945198007999)
                      ·
                        rfl

theorem cell23_4730355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_4730355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730355 prefixEnd_4730355 := by exact prefixLift 4730355
  have htrace : WordTrace (prefixWord ++ tailWord_4730355) baseStart_4730355 baseEnd_4730355 := by
    simpa [prefixWord, tailWord_4730355, baseEnd_4730355] using wordTrace_append hprefix tailTrace_4730355
  have hstable : (prefixWord ++ tailWord_4730355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730355).length < 2 ^ (prefixWord ++ tailWord_4730355).sum := by decide
  have hdescent : baseEnd_4730355 < baseStart_4730355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730362 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_4730362 : Nat := 118140960795 + 4730362 * 2 ^ 59
def prefixEnd_4730362 : Nat := 4983230072969 + 3 ^ 40 * 4730362 * 2
def baseEnd_4730362 : Nat := 809649791921175556873489

theorem tailTrace_4730362 : CollatzResearch.WordTrace tailWord_4730362 prefixEnd_4730362 809649791921175556873489 := by
  unfold tailWord_4730362
  simp only [CollatzResearch.WordTrace]
  refine ⟨43132619022178457588994335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115020317392475886903984893 43132619022178457588994335)
  ·
    refine ⟨64698928533267686383491503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43132619022178457588994335 64698928533267686383491503)
    ·
      refine ⟨97048392799901529575237255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64698928533267686383491503 97048392799901529575237255)
      ·
        refine ⟨145572589199852294362855883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97048392799901529575237255 145572589199852294362855883)
        ·
          refine ⟨218358883799778441544283825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145572589199852294362855883 218358883799778441544283825)
          ·
            refine ⟨163769162849833831158212869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218358883799778441544283825 163769162849833831158212869)
            ·
              refine ⟨30706718034343843342164913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163769162849833831158212869 30706718034343843342164913)
              ·
                refine ⟨23030038525757882506623685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30706718034343843342164913 23030038525757882506623685)
                ·
                  refine ⟨4318132223579602969991941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23030038525757882506623685 4318132223579602969991941)
                  ·
                    refine ⟨809649791921175556873489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318132223579602969991941 809649791921175556873489)
                    ·
                      rfl

theorem cell23_4730362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_4730362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730362 prefixEnd_4730362 := by exact prefixLift 4730362
  have htrace : WordTrace (prefixWord ++ tailWord_4730362) baseStart_4730362 baseEnd_4730362 := by
    simpa [prefixWord, tailWord_4730362, baseEnd_4730362] using wordTrace_append hprefix tailTrace_4730362
  have hstable : (prefixWord ++ tailWord_4730362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730362).length < 2 ^ (prefixWord ++ tailWord_4730362).sum := by decide
  have hdescent : baseEnd_4730362 < baseStart_4730362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730379 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 4, 4]
def baseStart_4730379 : Nat := 118140960795 + 4730379 * 2 ^ 59
def prefixEnd_4730379 : Nat := 4983230072969 + 3 ^ 40 * 4730379 * 2
def baseEnd_4730379 : Nat := 809652701644884368035963

theorem tailTrace_4730379 : CollatzResearch.WordTrace tailWord_4730379 prefixEnd_4730379 809652701644884368035963 := by
  unfold tailWord_4730379
  simp only [CollatzResearch.WordTrace]
  refine ⟨172531096129652242259346191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115020730753101494839564127 172531096129652242259346191)
  ·
    refine ⟨258796644194478363389019287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172531096129652242259346191 258796644194478363389019287)
    ·
      refine ⟨388194966291717545083528931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258796644194478363389019287 388194966291717545083528931)
      ·
        refine ⟨582292449437576317625293397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388194966291717545083528931 582292449437576317625293397)
        ·
          refine ⟨6823739641846597472171407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 582292449437576317625293397 6823739641846597472171407)
          ·
            refine ⟨10235609462769896208257111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823739641846597472171407 10235609462769896208257111)
            ·
              refine ⟨15353414194154844312385667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10235609462769896208257111 15353414194154844312385667)
              ·
                refine ⟨23030121291232266468578501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15353414194154844312385667 23030121291232266468578501)
                ·
                  refine ⟨4318147742106049962858469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23030121291232266468578501 4318147742106049962858469)
                  ·
                    refine ⟨809652701644884368035963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318147742106049962858469 809652701644884368035963)
                    ·
                      rfl

theorem cell23_4730379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 4].length) (baseStart_4730379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730379 prefixEnd_4730379 := by exact prefixLift 4730379
  have htrace : WordTrace (prefixWord ++ tailWord_4730379) baseStart_4730379 baseEnd_4730379 := by
    simpa [prefixWord, tailWord_4730379, baseEnd_4730379] using wordTrace_append hprefix tailTrace_4730379
  have hstable : (prefixWord ++ tailWord_4730379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730379).length < 2 ^ (prefixWord ++ tailWord_4730379).sum := by decide
  have hdescent : baseEnd_4730379 < baseStart_4730379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730396 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_4730396 : Nat := 118140960795 + 4730396 * 2 ^ 59
def prefixEnd_4730396 : Nat := 4983230072969 + 3 ^ 40 * 4730396 * 2
def baseEnd_4730396 : Nat := 809655611368593179198437

theorem tailTrace_4730396 : CollatzResearch.WordTrace tailWord_4730396 prefixEnd_4730396 809655611368593179198437 := by
  unfold tailWord_4730396
  simp only [CollatzResearch.WordTrace]
  refine ⟨86265858085295327081357521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115021144113727102775143361 86265858085295327081357521)
  ·
    refine ⟨64699393563971495311018141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86265858085295327081357521 64699393563971495311018141)
    ·
      refine ⟨24262272586489310741631803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64699393563971495311018141 24262272586489310741631803)
      ·
        refine ⟨36393408879733966112447705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24262272586489310741631803 36393408879733966112447705)
        ·
          refine ⟨27295056659800474584335779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36393408879733966112447705 27295056659800474584335779)
          ·
            refine ⟨40942584989700711876503669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27295056659800474584335779 40942584989700711876503669)
            ·
              refine ⟨3838367342784441738422219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40942584989700711876503669 3838367342784441738422219)
              ·
                refine ⟨5757551014176662607633329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3838367342784441738422219 5757551014176662607633329)
                ·
                  refine ⟨4318163260632496955724997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5757551014176662607633329 4318163260632496955724997)
                  ·
                    refine ⟨809655611368593179198437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318163260632496955724997 809655611368593179198437)
                    ·
                      rfl

theorem cell23_4730396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_4730396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730396 prefixEnd_4730396 := by exact prefixLift 4730396
  have htrace : WordTrace (prefixWord ++ tailWord_4730396) baseStart_4730396 baseEnd_4730396 := by
    simpa [prefixWord, tailWord_4730396, baseEnd_4730396] using wordTrace_append hprefix tailTrace_4730396
  have hstable : (prefixWord ++ tailWord_4730396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730396).length < 2 ^ (prefixWord ++ tailWord_4730396).sum := by decide
  have hdescent : baseEnd_4730396 < baseStart_4730396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730419 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 3]
def baseStart_4730419 : Nat := 118140960795 + 4730419 * 2 ^ 59
def prefixEnd_4730419 : Nat := 4983230072969 + 3 ^ 40 * 4730419 * 2
def baseEnd_4730419 : Nat := 2428978644160832947607705

theorem tailTrace_4730419 : CollatzResearch.WordTrace tailWord_4730419 prefixEnd_4730419 2428978644160832947607705 := by
  unfold tailWord_4730419
  simp only [CollatzResearch.WordTrace]
  refine ⟨172532555049507329090802311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115021703366338219393868207 172532555049507329090802311)
  ·
    refine ⟨258798832574260993636203467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172532555049507329090802311 258798832574260993636203467)
    ·
      refine ⟨388198248861391490454305201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258798832574260993636203467 388198248861391490454305201)
      ·
        refine ⟨291148686646043617840728901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388198248861391490454305201 291148686646043617840728901)
        ·
          refine ⟨54590378746133178345136669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291148686646043617840728901 54590378746133178345136669)
          ·
            refine ⟨20471392029799941879426251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54590378746133178345136669 20471392029799941879426251)
            ·
              refine ⟨30707088044699912819139377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20471392029799941879426251 30707088044699912819139377)
              ·
                refine ⟨23030316033524934614354533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30707088044699912819139377 23030316033524934614354533)
                ·
                  refine ⟨4318184256285925240191475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23030316033524934614354533 4318184256285925240191475)
                  ·
                    refine ⟨6477276384428887860287213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4318184256285925240191475 6477276384428887860287213)
                    ·
                      refine ⟨2428978644160832947607705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6477276384428887860287213 2428978644160832947607705)
                      ·
                        rfl

theorem cell23_4730419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 3].length) (baseStart_4730419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730419 prefixEnd_4730419 := by exact prefixLift 4730419
  have htrace : WordTrace (prefixWord ++ tailWord_4730419) baseStart_4730419 baseEnd_4730419 := by
    simpa [prefixWord, tailWord_4730419, baseEnd_4730419] using wordTrace_append hprefix tailTrace_4730419
  have hstable : (prefixWord ++ tailWord_4730419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730419).length < 2 ^ (prefixWord ++ tailWord_4730419).sum := by decide
  have hdescent : baseEnd_4730419 < baseStart_4730419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730442 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_4730442 : Nat := 118140960795 + 4730442 * 2 ^ 59
def prefixEnd_4730442 : Nat := 4983230072969 + 3 ^ 40 * 4730442 * 2
def baseEnd_4730442 : Nat := 2428990454215886357620099

theorem tailTrace_4730442 : CollatzResearch.WordTrace tailWord_4730442 prefixEnd_4730442 2428990454215886357620099 := by
  unfold tailWord_4730442
  simp only [CollatzResearch.WordTrace]
  refine ⟨43133348482106001004722395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115022262618949336012593053 43133348482106001004722395)
  ·
    refine ⟨64700022723159001507083593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43133348482106001004722395 64700022723159001507083593)
    ·
      refine ⟨48525017042369251130312695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64700022723159001507083593 48525017042369251130312695)
      ·
        refine ⟨72787525563553876695469043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48525017042369251130312695 72787525563553876695469043)
        ·
          refine ⟨109181288345330815043203565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72787525563553876695469043 109181288345330815043203565)
          ·
            refine ⟨40942983129499055641201337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109181288345330815043203565 40942983129499055641201337)
            ·
              refine ⟨30707237347124291730901003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40942983129499055641201337 30707237347124291730901003)
              ·
                refine ⟨46060856020686437596351505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30707237347124291730901003 46060856020686437596351505)
                ·
                  refine ⟨34545642015514828197263629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46060856020686437596351505 34545642015514828197263629)
                  ·
                    refine ⟨12954615755818060573973861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34545642015514828197263629 12954615755818060573973861)
                    ·
                      refine ⟨2428990454215886357620099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12954615755818060573973861 2428990454215886357620099)
                      ·
                        rfl

theorem cell23_4730442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_4730442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730442 prefixEnd_4730442 := by exact prefixLift 4730442
  have htrace : WordTrace (prefixWord ++ tailWord_4730442) baseStart_4730442 baseEnd_4730442 := by
    simpa [prefixWord, tailWord_4730442, baseEnd_4730442] using wordTrace_append hprefix tailTrace_4730442
  have hstable : (prefixWord ++ tailWord_4730442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730442).length < 2 ^ (prefixWord ++ tailWord_4730442).sum := by decide
  have hdescent : baseEnd_4730442 < baseStart_4730442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730452 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_4730452 : Nat := 118140960795 + 4730452 * 2 ^ 59
def prefixEnd_4730452 : Nat := 4983230072969 + 3 ^ 40 * 4730452 * 2
def baseEnd_4730452 : Nat := 809665196340810439498351

theorem tailTrace_4730452 : CollatzResearch.WordTrace tailWord_4730452 prefixEnd_4730452 809665196340810439498351 := by
  unfold tailWord_4730452
  simp only [CollatzResearch.WordTrace]
  refine ⟨86266879329193887863376805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115022505772258517151169073 86266879329193887863376805)
  ·
    refine ⟨16175039874223853974383151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86266879329193887863376805 16175039874223853974383151)
    ·
      refine ⟨24262559811335780961574727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16175039874223853974383151 24262559811335780961574727)
      ·
        refine ⟨36393839717003671442362091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24262559811335780961574727 36393839717003671442362091)
        ·
          refine ⟨54590759575505507163543137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36393839717003671442362091 54590759575505507163543137)
          ·
            refine ⟨40943069681629130372657353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54590759575505507163543137 40943069681629130372657353)
            ·
              refine ⟨30707302261221847779493015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40943069681629130372657353 30707302261221847779493015)
              ·
                refine ⟨46060953391832771669239523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30707302261221847779493015 46060953391832771669239523)
                ·
                  refine ⟨69091430087749157503859285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46060953391832771669239523 69091430087749157503859285)
                  ·
                    refine ⟨809665196340810439498351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69091430087749157503859285 809665196340810439498351)
                    ·
                      rfl

theorem cell23_4730452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_4730452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730452 prefixEnd_4730452 := by exact prefixLift 4730452
  have htrace : WordTrace (prefixWord ++ tailWord_4730452) baseStart_4730452 baseEnd_4730452 := by
    simpa [prefixWord, tailWord_4730452, baseEnd_4730452] using wordTrace_append hprefix tailTrace_4730452
  have hstable : (prefixWord ++ tailWord_4730452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730452).length < 2 ^ (prefixWord ++ tailWord_4730452).sum := by decide
  have hdescent : baseEnd_4730452 < baseStart_4730452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730493 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_4730493 : Nat := 118140960795 + 4730493 * 2 ^ 59
def prefixEnd_4730493 : Nat := 4983230072969 + 3 ^ 40 * 4730493 * 2
def baseEnd_4730493 : Nat := 2429016641729265658082365

theorem tailTrace_4730493 : CollatzResearch.WordTrace tailWord_4730493 prefixEnd_4730493 2429016641729265658082365 := by
  unfold tailWord_4730493
  simp only [CollatzResearch.WordTrace]
  refine ⟨172535254051239239728996133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115023502700826159819330755 172535254051239239728996133)
  ·
    refine ⟨32350360134607357449186775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172535254051239239728996133 32350360134607357449186775)
    ·
      refine ⟨48525540201911036173780163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32350360134607357449186775 48525540201911036173780163)
      ·
        refine ⟨72788310302866554260670245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48525540201911036173780163 72788310302866554260670245)
        ·
          refine ⟨13647808181787478923875671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72788310302866554260670245 13647808181787478923875671)
          ·
            refine ⟨20471712272681218385813507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13647808181787478923875671 20471712272681218385813507)
            ·
              refine ⟨30707568409021827578720261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20471712272681218385813507 30707568409021827578720261)
              ·
                refine ⟨5757669076691592671010049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30707568409021827578720261 5757669076691592671010049)
                ·
                  refine ⟨4318251807518694503257537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5757669076691592671010049 4318251807518694503257537)
                  ·
                    refine ⟨3238688855639020877443153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4318251807518694503257537 3238688855639020877443153)
                    ·
                      refine ⟨2429016641729265658082365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238688855639020877443153 2429016641729265658082365)
                      ·
                        rfl

theorem cell23_4730493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_4730493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730493 prefixEnd_4730493 := by exact prefixLift 4730493
  have htrace : WordTrace (prefixWord ++ tailWord_4730493) baseStart_4730493 baseEnd_4730493 := by
    simpa [prefixWord, tailWord_4730493, baseEnd_4730493] using wordTrace_append hprefix tailTrace_4730493
  have hstable : (prefixWord ++ tailWord_4730493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730493).length < 2 ^ (prefixWord ++ tailWord_4730493).sum := by decide
  have hdescent : baseEnd_4730493 < baseStart_4730493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730512 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 4, 5]
def baseStart_4730512 : Nat := 118140960795 + 4730512 * 2 ^ 59
def prefixEnd_4730512 : Nat := 4983230072969 + 3 ^ 40 * 4730512 * 2
def baseEnd_4730512 : Nat := 809675465953900361248259

theorem tailTrace_4730512 : CollatzResearch.WordTrace tailWord_4730512 prefixEnd_4730512 809675465953900361248259 := by
  unfold tailWord_4730512
  simp only [CollatzResearch.WordTrace]
  refine ⟨86267973519085202986968895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115023964692113603982625193 86267973519085202986968895)
  ·
    refine ⟨129401960278627804480453343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86267973519085202986968895 129401960278627804480453343)
    ·
      refine ⟨194102940417941706720680015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129401960278627804480453343 194102940417941706720680015)
      ·
        refine ⟨291154410626912560081020023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194102940417941706720680015 291154410626912560081020023)
        ·
          refine ⟨436731615940368840121530035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291154410626912560081020023 436731615940368840121530035)
          ·
            refine ⟨655097423910553260182295053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436731615940368840121530035 655097423910553260182295053)
            ·
              refine ⟨245661533966457472568360645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 655097423910553260182295053 245661533966457472568360645)
              ·
                refine ⟨46061537618710776106567621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245661533966457472568360645 46061537618710776106567621)
                ·
                  refine ⟨8636538303508270519981429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46061537618710776106567621 8636538303508270519981429)
                  ·
                    refine ⟨809675465953900361248259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8636538303508270519981429 809675465953900361248259)
                    ·
                      rfl

theorem cell23_4730512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_4730512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730512 prefixEnd_4730512 := by exact prefixLift 4730512
  have htrace : WordTrace (prefixWord ++ tailWord_4730512) baseStart_4730512 baseEnd_4730512 := by
    simpa [prefixWord, tailWord_4730512, baseEnd_4730512] using wordTrace_append hprefix tailTrace_4730512
  have hstable : (prefixWord ++ tailWord_4730512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730512).length < 2 ^ (prefixWord ++ tailWord_4730512).sum := by decide
  have hdescent : baseEnd_4730512 < baseStart_4730512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730516 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 7]
def baseStart_4730516 : Nat := 118140960795 + 4730516 * 2 ^ 59
def prefixEnd_4730516 : Nat := 4983230072969 + 3 ^ 40 * 4730516 * 2
def baseEnd_4730516 : Nat := 269892050198257674232751

theorem tailTrace_4730516 : CollatzResearch.WordTrace tailWord_4730516 prefixEnd_4730516 269892050198257674232751 := by
  unfold tailWord_4730516
  simp only [CollatzResearch.WordTrace]
  refine ⟨86268046465077957328541701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115024061953437276438055601 86268046465077957328541701)
  ·
    refine ⟨16175258712202116999101569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86268046465077957328541701 16175258712202116999101569)
    ·
      refine ⟨12131444034151587749326177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16175258712202116999101569 12131444034151587749326177)
      ·
        refine ⟨9098583025613690811994633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12131444034151587749326177 9098583025613690811994633)
        ·
          refine ⟨6823937269210268108995975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9098583025613690811994633 6823937269210268108995975)
          ·
            refine ⟨10235905903815402163493963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823937269210268108995975 10235905903815402163493963)
            ·
              refine ⟨15353858855723103245240945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10235905903815402163493963 15353858855723103245240945)
              ·
                refine ⟨11515394141792327433930709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15353858855723103245240945 11515394141792327433930709)
                ·
                  refine ⟨269892050198257674232751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11515394141792327433930709 269892050198257674232751)
                  ·
                    rfl

theorem cell23_4730516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_4730516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730516 prefixEnd_4730516 := by exact prefixLift 4730516
  have htrace : WordTrace (prefixWord ++ tailWord_4730516) baseStart_4730516 baseEnd_4730516 := by
    simpa [prefixWord, tailWord_4730516, baseEnd_4730516] using wordTrace_append hprefix tailTrace_4730516
  have hstable : (prefixWord ++ tailWord_4730516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730516).length < 2 ^ (prefixWord ++ tailWord_4730516).sum := by decide
  have hdescent : baseEnd_4730516 < baseStart_4730516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730529 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 1, 7]
def baseStart_4730529 : Nat := 118140960795 + 4730529 * 2 ^ 59
def prefixEnd_4730529 : Nat := 4983230072969 + 3 ^ 40 * 4730529 * 2
def baseEnd_4730529 : Nat := 809678375677609172410733

theorem tailTrace_4730529 : CollatzResearch.WordTrace tailWord_4730529 prefixEnd_4730529 809678375677609172410733 := by
  unfold tailWord_4730529
  simp only [CollatzResearch.WordTrace]
  refine ⟨172536567079108817877306641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115024378052739211918204427 172536567079108817877306641)
  ·
    refine ⟨129402425309331613407979981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172536567079108817877306641 129402425309331613407979981)
    ·
      refine ⟨48525909490999355027992493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129402425309331613407979981 48525909490999355027992493)
      ·
        refine ⟨18197216059124758135497185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48525909490999355027992493 18197216059124758135497185)
        ·
          refine ⟨13647912044343568601622889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18197216059124758135497185 13647912044343568601622889)
          ·
            refine ⟨10235934033257676451217167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13647912044343568601622889 10235934033257676451217167)
            ·
              refine ⟨15353901049886514676825751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10235934033257676451217167 15353901049886514676825751)
              ·
                refine ⟨23030851574829772015238627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15353901049886514676825751 23030851574829772015238627)
                ·
                  refine ⟨34546277362244658022857941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23030851574829772015238627 34546277362244658022857941)
                  ·
                    refine ⟨809678375677609172410733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34546277362244658022857941 809678375677609172410733)
                    ·
                      rfl

theorem cell23_4730529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_4730529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730529 prefixEnd_4730529 := by exact prefixLift 4730529
  have htrace : WordTrace (prefixWord ++ tailWord_4730529) baseStart_4730529 baseEnd_4730529 := by
    simpa [prefixWord, tailWord_4730529, baseEnd_4730529] using wordTrace_append hprefix tailTrace_4730529
  have hstable : (prefixWord ++ tailWord_4730529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730529).length < 2 ^ (prefixWord ++ tailWord_4730529).sum := by decide
  have hdescent : baseEnd_4730529 < baseStart_4730529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730552 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_4730552 : Nat := 118140960795 + 4730552 * 2 ^ 59
def prefixEnd_4730552 : Nat := 4983230072969 + 3 ^ 40 * 4730552 * 2
def baseEnd_4730552 : Nat := 2429046937087880927244593

theorem tailTrace_4730552 : CollatzResearch.WordTrace tailWord_4730552 prefixEnd_4730552 2429046937087880927244593 := by
  unfold tailWord_4730552
  simp only [CollatzResearch.WordTrace]
  refine ⟨86268702979012746402696955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115024937305350328536929273 86268702979012746402696955)
  ·
    refine ⟨129403054468519119604045433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86268702979012746402696955 129403054468519119604045433)
    ·
      refine ⟨97052290851389339703034075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129403054468519119604045433 97052290851389339703034075)
      ·
        refine ⟨145578436277084009554551113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97052290851389339703034075 145578436277084009554551113)
        ·
          refine ⟨109183827207813007165913335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145578436277084009554551113 109183827207813007165913335)
          ·
            refine ⟨163775740811719510748870003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109183827207813007165913335 163775740811719510748870003)
            ·
              refine ⟨245663611217579266123305005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163775740811719510748870003 245663611217579266123305005)
              ·
                refine ⟨92123854206592224796239377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245663611217579266123305005 92123854206592224796239377)
                ·
                  refine ⟨69092890654944168597179533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92123854206592224796239377 69092890654944168597179533)
                  ·
                    refine ⟨25909833995604063223942325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69092890654944168597179533 25909833995604063223942325)
                    ·
                      refine ⟨2429046937087880927244593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25909833995604063223942325 2429046937087880927244593)
                      ·
                        rfl

theorem cell23_4730552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_4730552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730552 prefixEnd_4730552 := by exact prefixLift 4730552
  have htrace : WordTrace (prefixWord ++ tailWord_4730552) baseStart_4730552 baseEnd_4730552 := by
    simpa [prefixWord, tailWord_4730552, baseEnd_4730552] using wordTrace_append hprefix tailTrace_4730552
  have hstable : (prefixWord ++ tailWord_4730552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730552).length < 2 ^ (prefixWord ++ tailWord_4730552).sum := by decide
  have hdescent : baseEnd_4730552 < baseStart_4730552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730610 : List Nat := [3, 2, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_4730610 : Nat := 118140960795 + 4730610 * 2 ^ 59
def prefixEnd_4730610 : Nat := 4983230072969 + 3 ^ 40 * 4730610 * 2
def baseEnd_4730610 : Nat := 809692239655280566773109

theorem tailTrace_4730610 : CollatzResearch.WordTrace tailWord_4730610 prefixEnd_4730610 809692239655280566773109 := by
  unfold tailWord_4730610
  simp only [CollatzResearch.WordTrace]
  refine ⟨43134880347953842177751321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115026347594543579140670189 43134880347953842177751321)
  ·
    refine ⟨32351160260965381633313491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43134880347953842177751321 32351160260965381633313491)
    ·
      refine ⟨48526740391448072449970237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32351160260965381633313491 48526740391448072449970237)
      ·
        refine ⟨18197527646793027168738839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48526740391448072449970237 18197527646793027168738839)
        ·
          refine ⟨27296291470189540753108259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18197527646793027168738839 27296291470189540753108259)
          ·
            refine ⟨40944437205284311129662389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27296291470189540753108259 40944437205284311129662389)
            ·
              refine ⟨3838540987995404168405849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40944437205284311129662389 3838540987995404168405849)
              ·
                refine ⟨2878905740996553126304387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3838540987995404168405849 2878905740996553126304387)
                ·
                  refine ⟨4318358611494829689456581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878905740996553126304387 4318358611494829689456581)
                  ·
                    refine ⟨809692239655280566773109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318358611494829689456581 809692239655280566773109)
                    ·
                      rfl

theorem cell23_4730610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_4730610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730610 prefixEnd_4730610 := by exact prefixLift 4730610
  have htrace : WordTrace (prefixWord ++ tailWord_4730610) baseStart_4730610 baseEnd_4730610 := by
    simpa [prefixWord, tailWord_4730610, baseEnd_4730610] using wordTrace_append hprefix tailTrace_4730610
  have hstable : (prefixWord ++ tailWord_4730610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730610).length < 2 ^ (prefixWord ++ tailWord_4730610).sum := by decide
  have hdescent : baseEnd_4730610 < baseStart_4730610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730616 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 3, 1, 3]
def baseStart_4730616 : Nat := 118140960795 + 4730616 * 2 ^ 59
def prefixEnd_4730616 : Nat := 4983230072969 + 3 ^ 40 * 4730616 * 2
def baseEnd_4730616 : Nat := 2429079799849768676844299

theorem tailTrace_4730616 : CollatzResearch.WordTrace tailWord_4730616 prefixEnd_4730616 2429079799849768676844299 := by
  unfold tailWord_4730616
  simp only [CollatzResearch.WordTrace]
  refine ⟨86269870114896815867861851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115026493486529087823815801 86269870114896815867861851)
  ·
    refine ⟨129404805172345223801792777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86269870114896815867861851 129404805172345223801792777)
    ·
      refine ⟨97053603879258917851344583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129404805172345223801792777 97053603879258917851344583)
      ·
        refine ⟨145580405818888376777016875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97053603879258917851344583 145580405818888376777016875)
        ·
          refine ⟨218370608728332565165525313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145580405818888376777016875 218370608728332565165525313)
          ·
            refine ⟨163777956546249423874143985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218370608728332565165525313 163777956546249423874143985)
            ·
              refine ⟨122833467409687067905607989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163777956546249423874143985 122833467409687067905607989)
              ·
                refine ⟨11515637569658162616150749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122833467409687067905607989 11515637569658162616150749)
                ·
                  refine ⟨4318364088621810981056531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11515637569658162616150749 4318364088621810981056531)
                  ·
                    refine ⟨6477546132932716471584797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4318364088621810981056531 6477546132932716471584797)
                    ·
                      refine ⟨2429079799849768676844299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6477546132932716471584797 2429079799849768676844299)
                      ·
                        rfl

theorem cell23_4730616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_4730616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730616 prefixEnd_4730616 := by exact prefixLift 4730616
  have htrace : WordTrace (prefixWord ++ tailWord_4730616) baseStart_4730616 baseEnd_4730616 := by
    simpa [prefixWord, tailWord_4730616, baseEnd_4730616] using wordTrace_append hprefix tailTrace_4730616
  have hstable : (prefixWord ++ tailWord_4730616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730616).length < 2 ^ (prefixWord ++ tailWord_4730616).sum := by decide
  have hdescent : baseEnd_4730616 < baseStart_4730616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730636 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_4730636 : Nat := 118140960795 + 4730636 * 2 ^ 59
def prefixEnd_4730636 : Nat := 4983230072969 + 3 ^ 40 * 4730636 * 2
def baseEnd_4730636 : Nat := 809696689820952866198069

theorem tailTrace_4730636 : CollatzResearch.WordTrace tailWord_4730636 prefixEnd_4730636 809696689820952866198069 := by
  unfold tailWord_4730636
  simp only [CollatzResearch.WordTrace]
  refine ⟨86270234844860587575725881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115026979793147450100967841 86270234844860587575725881)
  ·
    refine ⟨64702676133645440681794411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86270234844860587575725881 64702676133645440681794411)
    ·
      refine ⟨97054014200468161022691617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64702676133645440681794411 97054014200468161022691617)
      ·
        refine ⟨72790510650351120767018713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97054014200468161022691617 72790510650351120767018713)
        ·
          refine ⟨54592882987763340575264035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72790510650351120767018713 54592882987763340575264035)
          ·
            refine ⟨81889324481645010862896053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54592882987763340575264035 81889324481645010862896053)
            ·
              refine ⟨7677124170154219768396505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81889324481645010862896053 7677124170154219768396505)
              ·
                refine ⟨5757843127615664826297379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7677124170154219768396505 5757843127615664826297379)
                ·
                  refine ⟨8636764691423497239446069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5757843127615664826297379 8636764691423497239446069)
                  ·
                    refine ⟨809696689820952866198069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8636764691423497239446069 809696689820952866198069)
                    ·
                      rfl

theorem cell23_4730636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_4730636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730636 prefixEnd_4730636 := by exact prefixLift 4730636
  have htrace : WordTrace (prefixWord ++ tailWord_4730636) baseStart_4730636 baseEnd_4730636 := by
    simpa [prefixWord, tailWord_4730636, baseEnd_4730636] using wordTrace_append hprefix tailTrace_4730636
  have hstable : (prefixWord ++ tailWord_4730636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730636).length < 2 ^ (prefixWord ++ tailWord_4730636).sum := by decide
  have hdescent : baseEnd_4730636 < baseStart_4730636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730694 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4730694 : Nat := 118140960795 + 4730694 * 2 ^ 59
def prefixEnd_4730694 : Nat := 4983230072969 + 3 ^ 40 * 4730694 * 2
def baseEnd_4730694 : Nat := 2429119851340819371668941

theorem tailTrace_4730694 : CollatzResearch.WordTrace tailWord_4730694 prefixEnd_4730694 2429119851340819371668941 := by
  unfold tailWord_4730694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391955785109720345533223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115028390082340700704708757 5391955785109720345533223)
  ·
    refine ⟨8087933677664580518299835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5391955785109720345533223 8087933677664580518299835)
    ·
      refine ⟨12131900516496870777449753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8087933677664580518299835 12131900516496870777449753)
      ·
        refine ⟨9098925387372653083087315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12131900516496870777449753 9098925387372653083087315)
        ·
          refine ⟨13648388081058979624630973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9098925387372653083087315 13648388081058979624630973)
          ·
            refine ⟨5118145530397117359236615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13648388081058979624630973 5118145530397117359236615)
            ·
              refine ⟨7677218295595676038854923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5118145530397117359236615 7677218295595676038854923)
              ·
                refine ⟨11515827443393514058282385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7677218295595676038854923 11515827443393514058282385)
                ·
                  refine ⟨8636870582545135543711789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11515827443393514058282385 8636870582545135543711789)
                  ·
                    refine ⟨3238826468454425828891921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8636870582545135543711789 3238826468454425828891921)
                    ·
                      refine ⟨2429119851340819371668941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238826468454425828891921 2429119851340819371668941)
                      ·
                        rfl

theorem cell23_4730694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4730694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730694 prefixEnd_4730694 := by exact prefixLift 4730694
  have htrace : WordTrace (prefixWord ++ tailWord_4730694) baseStart_4730694 baseEnd_4730694 := by
    simpa [prefixWord, tailWord_4730694, baseEnd_4730694] using wordTrace_append hprefix tailTrace_4730694
  have hstable : (prefixWord ++ tailWord_4730694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730694).length < 2 ^ (prefixWord ++ tailWord_4730694).sum := by decide
  have hdescent : baseEnd_4730694 < baseStart_4730694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730696 : List Nat := [2, 1, 3, 1, 1, 5, 3, 7]
def baseStart_4730696 : Nat := 118140960795 + 4730696 * 2 ^ 59
def prefixEnd_4730696 : Nat := 4983230072969 + 3 ^ 40 * 4730696 * 2
def baseEnd_4730696 : Nat := 89967439937115865327553

theorem tailTrace_4730696 : CollatzResearch.WordTrace tailWord_4730696 prefixEnd_4730696 89967439937115865327553 := by
  unfold tailWord_4730696
  simp only [CollatzResearch.WordTrace]
  refine ⟨86271329034751902699317971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115028438713002536932423961 86271329034751902699317971)
  ·
    refine ⟨129406993552127854048976957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86271329034751902699317971 129406993552127854048976957)
    ·
      refine ⟨48527622582047945268366359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129406993552127854048976957 48527622582047945268366359)
      ·
        refine ⟨72791433873071917902549539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48527622582047945268366359 72791433873071917902549539)
        ·
          refine ⟨109187150809607876853824309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72791433873071917902549539 109187150809607876853824309)
          ·
            refine ⟨10236295388400738455046029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109187150809607876853824309 10236295388400738455046029)
            ·
              refine ⟨3838610770650276920642261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10236295388400738455046029 3838610770650276920642261)
              ·
                refine ⟨89967439937115865327553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3838610770650276920642261 89967439937115865327553)
                ·
                  rfl

theorem cell23_4730696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 7].length) (baseStart_4730696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730696 prefixEnd_4730696 := by exact prefixLift 4730696
  have htrace : WordTrace (prefixWord ++ tailWord_4730696) baseStart_4730696 baseEnd_4730696 := by
    simpa [prefixWord, tailWord_4730696, baseEnd_4730696] using wordTrace_append hprefix tailTrace_4730696
  have hstable : (prefixWord ++ tailWord_4730696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730696).length < 2 ^ (prefixWord ++ tailWord_4730696).sum := by decide
  have hdescent : baseEnd_4730696 < baseStart_4730696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730729 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_4730729 : Nat := 118140960795 + 4730729 * 2 ^ 59
def prefixEnd_4730729 : Nat := 4983230072969 + 3 ^ 40 * 4730729 * 2
def baseEnd_4730729 : Nat := 2429137823163726734731279

theorem tailTrace_4730729 : CollatzResearch.WordTrace tailWord_4730729 prefixEnd_4730729 2429137823163726734731279 := by
  unfold tailWord_4730729
  simp only [CollatzResearch.WordTrace]
  refine ⟨172543861678384252034587241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115029241118922834689724827 172543861678384252034587241)
  ·
    refine ⟨129407896258788189025940431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172543861678384252034587241 129407896258788189025940431)
    ·
      refine ⟨194111844388182283538910647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129407896258788189025940431 194111844388182283538910647)
      ·
        refine ⟨291167766582273425308365971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194111844388182283538910647 291167766582273425308365971)
        ·
          refine ⟨436751649873410137962548957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291167766582273425308365971 436751649873410137962548957)
          ·
            refine ⟨163781868702528801735955859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 436751649873410137962548957 163781868702528801735955859)
            ·
              refine ⟨245672803053793202603933789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163781868702528801735955859 245672803053793202603933789)
              ·
                refine ⟨92127301145172450976475171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245672803053793202603933789 92127301145172450976475171)
                ·
                  refine ⟨138190951717758676464712757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92127301145172450976475171 138190951717758676464712757)
                  ·
                    refine ⟨12955401723539875918566821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 138190951717758676464712757 12955401723539875918566821)
                    ·
                      refine ⟨2429137823163726734731279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12955401723539875918566821 2429137823163726734731279)
                      ·
                        rfl

theorem cell23_4730729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_4730729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730729 prefixEnd_4730729 := by exact prefixLift 4730729
  have htrace : WordTrace (prefixWord ++ tailWord_4730729) baseStart_4730729 baseEnd_4730729 := by
    simpa [prefixWord, tailWord_4730729, baseEnd_4730729] using wordTrace_append hprefix tailTrace_4730729
  have hstable : (prefixWord ++ tailWord_4730729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730729).length < 2 ^ (prefixWord ++ tailWord_4730729).sum := by decide
  have hdescent : baseEnd_4730729 < baseStart_4730729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730733 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_4730733 : Nat := 118140960795 + 4730733 * 2 ^ 59
def prefixEnd_4730733 : Nat := 4983230072969 + 3 ^ 40 * 4730733 * 2
def baseEnd_4730733 : Nat := 2429139877086344719081261

theorem tailTrace_4730733 : CollatzResearch.WordTrace tailWord_4730733 prefixEnd_4730733 2429139877086344719081261 := by
  unfold tailWord_4730733
  simp only [CollatzResearch.WordTrace]
  refine ⟨172544007570369760717732853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115029338380246507145155235 172544007570369760717732853)
  ·
    refine ⟨16176000709722165067287455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172544007570369760717732853 16176000709722165067287455)
    ·
      refine ⟨24264001064583247600931183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16176000709722165067287455 24264001064583247600931183)
      ·
        refine ⟨36396001596874871401396775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24264001064583247600931183 36396001596874871401396775)
        ·
          refine ⟨54594002395312307102095163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36396001596874871401396775 54594002395312307102095163)
          ·
            refine ⟨81891003592968460653142745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54594002395312307102095163 81891003592968460653142745)
            ·
              refine ⟨61418252694726345489857059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81891003592968460653142745 61418252694726345489857059)
              ·
                refine ⟨92127379042089518234785589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61418252694726345489857059 92127379042089518234785589)
                ·
                  refine ⟨8636941785195892334511149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92127379042089518234785589 8636941785195892334511149)
                  ·
                    refine ⟨3238853169448459625441681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8636941785195892334511149 3238853169448459625441681)
                    ·
                      refine ⟨2429139877086344719081261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238853169448459625441681 2429139877086344719081261)
                      ·
                        rfl

theorem cell23_4730733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_4730733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730733 prefixEnd_4730733 := by exact prefixLift 4730733
  have htrace : WordTrace (prefixWord ++ tailWord_4730733) baseStart_4730733 baseEnd_4730733 := by
    simpa [prefixWord, tailWord_4730733, baseEnd_4730733] using wordTrace_append hprefix tailTrace_4730733
  have hstable : (prefixWord ++ tailWord_4730733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730733).length < 2 ^ (prefixWord ++ tailWord_4730733).sum := by decide
  have hdescent : baseEnd_4730733 < baseStart_4730733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730769 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 9]
def baseStart_4730769 : Nat := 118140960795 + 4730769 * 2 ^ 59
def prefixEnd_4730769 : Nat := 4983230072969 + 3 ^ 40 * 4730769 * 2
def baseEnd_4730769 : Nat := 269906484709989619803455

theorem tailTrace_4730769 : CollatzResearch.WordTrace tailWord_4730769 prefixEnd_4730769 269906484709989619803455 := by
  unfold tailWord_4730769
  simp only [CollatzResearch.WordTrace]
  refine ⟨172545320598239338866043361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115030213732159559244028907 172545320598239338866043361)
  ·
    refine ⟨129408990448679504149532521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172545320598239338866043361 129408990448679504149532521)
    ·
      refine ⟨97056742836509628112149391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129408990448679504149532521 97056742836509628112149391)
      ·
        refine ⟨145585114254764442168224087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97056742836509628112149391 145585114254764442168224087)
        ·
          refine ⟨218377671382146663252336131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145585114254764442168224087 218377671382146663252336131)
          ·
            refine ⟨327566507073219994878504197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218377671382146663252336131 327566507073219994878504197)
            ·
              refine ⟨61418720076228749039719537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327566507073219994878504197 61418720076228749039719537)
              ·
                refine ⟨46064040057171561779789653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61418720076228749039719537 46064040057171561779789653)
                ·
                  refine ⟨269906484709989619803455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46064040057171561779789653 269906484709989619803455)
                  ·
                    rfl

theorem cell23_4730769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 9].length) (baseStart_4730769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730769 prefixEnd_4730769 := by exact prefixLift 4730769
  have htrace : WordTrace (prefixWord ++ tailWord_4730769) baseStart_4730769 baseEnd_4730769 := by
    simpa [prefixWord, tailWord_4730769, baseEnd_4730769] using wordTrace_append hprefix tailTrace_4730769
  have hstable : (prefixWord ++ tailWord_4730769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730769).length < 2 ^ (prefixWord ++ tailWord_4730769).sum := by decide
  have hdescent : baseEnd_4730769 < baseStart_4730769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730826 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_4730826 : Nat := 118140960795 + 4730826 * 2 ^ 59
def prefixEnd_4730826 : Nat := 4983230072969 + 3 ^ 40 * 4730826 * 2
def baseEnd_4730826 : Nat := 2429187630787212855218333

theorem tailTrace_4730826 : CollatzResearch.WordTrace tailWord_4730826 prefixEnd_4730826 2429187630787212855218333 := by
  unfold tailWord_4730826
  simp only [CollatzResearch.WordTrace]
  refine ⟨43136849889758209400217083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115031599706021891733912221 43136849889758209400217083)
  ·
    refine ⟨64705274834637314100325625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43136849889758209400217083 64705274834637314100325625)
    ·
      refine ⟨48528956125977985575244219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64705274834637314100325625 48528956125977985575244219)
      ·
        refine ⟨72793434188966978362866329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48528956125977985575244219 72793434188966978362866329)
        ·
          refine ⟨54595075641725233772149747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72793434188966978362866329 54595075641725233772149747)
          ·
            refine ⟨81892613462587850658224621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54595075641725233772149747 81892613462587850658224621)
            ·
              refine ⟨30709730048470443996834233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81892613462587850658224621 30709730048470443996834233)
              ·
                refine ⟨23032297536352832997625675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30709730048470443996834233 23032297536352832997625675)
                ·
                  refine ⟨34548446304529249496438513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23032297536352832997625675 34548446304529249496438513)
                  ·
                    refine ⟨25911334728396937122328885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34548446304529249496438513 25911334728396937122328885)
                    ·
                      refine ⟨2429187630787212855218333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25911334728396937122328885 2429187630787212855218333)
                      ·
                        rfl

theorem cell23_4730826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_4730826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730826 prefixEnd_4730826 := by exact prefixLift 4730826
  have htrace : WordTrace (prefixWord ++ tailWord_4730826) baseStart_4730826 baseEnd_4730826 := by
    simpa [prefixWord, tailWord_4730826, baseEnd_4730826] using wordTrace_append hprefix tailTrace_4730826
  have hstable : (prefixWord ++ tailWord_4730826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730826).length < 2 ^ (prefixWord ++ tailWord_4730826).sum := by decide
  have hdescent : baseEnd_4730826 < baseStart_4730826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730837 : List Nat := [1, 3, 2, 3, 2, 3, 2, 2, 5]
def baseStart_4730837 : Nat := 118140960795 + 4730837 * 2 ^ 59
def prefixEnd_4730837 : Nat := 4983230072969 + 3 ^ 40 * 4730837 * 2
def baseEnd_4730837 : Nat := 269910364341601368020087

theorem tailTrace_4730837 : CollatzResearch.WordTrace tailWord_4730837 prefixEnd_4730837 269910364341601368020087 := by
  unfold tailWord_4730837
  simp only [CollatzResearch.WordTrace]
  refine ⟨172547800761992986479518765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115031867174661990986345843 172547800761992986479518765)
  ·
    refine ⟨64705425285747369929819537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172547800761992986479518765 64705425285747369929819537)
    ·
      refine ⟨48529068964310527447364653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64705425285747369929819537 48529068964310527447364653)
      ·
        refine ⟨18198400861616447792761745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48529068964310527447364653 18198400861616447792761745)
        ·
          refine ⟨13648800646212335844571309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18198400861616447792761745 13648800646212335844571309)
          ·
            refine ⟨5118300242329625941714241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13648800646212335844571309 5118300242329625941714241)
            ·
              refine ⟨3838725181747219456285681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5118300242329625941714241 3838725181747219456285681)
              ·
                refine ⟨2879043886310414592214261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3838725181747219456285681 2879043886310414592214261)
                ·
                  refine ⟨269910364341601368020087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2879043886310414592214261 269910364341601368020087)
                  ·
                    rfl

theorem cell23_4730837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_4730837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730837 prefixEnd_4730837 := by exact prefixLift 4730837
  have htrace : WordTrace (prefixWord ++ tailWord_4730837) baseStart_4730837 baseEnd_4730837 := by
    simpa [prefixWord, tailWord_4730837, baseEnd_4730837] using wordTrace_append hprefix tailTrace_4730837
  have hstable : (prefixWord ++ tailWord_4730837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730837).length < 2 ^ (prefixWord ++ tailWord_4730837).sum := by decide
  have hdescent : baseEnd_4730837 < baseStart_4730837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730863 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 3, 4]
def baseStart_4730863 : Nat := 118140960795 + 4730863 * 2 ^ 59
def prefixEnd_4730863 : Nat := 4983230072969 + 3 ^ 40 * 4730863 * 2
def baseEnd_4730863 : Nat := 809735543190476403485221

theorem tailTrace_4730863 : CollatzResearch.WordTrace tailWord_4730863 prefixEnd_4730863 809735543190476403485221 := by
  unfold tailWord_4730863
  simp only [CollatzResearch.WordTrace]
  refine ⟨172548749059898792919965243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115032499373265861946643495 172548749059898792919965243)
  ·
    refine ⟨258823123589848189379947865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172548749059898792919965243 258823123589848189379947865)
    ·
      refine ⟨194117342692386142034960899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258823123589848189379947865 194117342692386142034960899)
      ·
        refine ⟨291176014038579213052441349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194117342692386142034960899 291176014038579213052441349)
        ·
          refine ⟨54595502632233602447332753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 291176014038579213052441349 54595502632233602447332753)
          ·
            refine ⟨40946626974175201835499565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54595502632233602447332753 40946626974175201835499565)
            ·
              refine ⟨15354985115315700688312337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40946626974175201835499565 15354985115315700688312337)
              ·
                refine ⟨11516238836486775516234253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15354985115315700688312337 11516238836486775516234253)
                ·
                  refine ⟨4318589563682540818587845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11516238836486775516234253 4318589563682540818587845)
                  ·
                    refine ⟨809735543190476403485221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318589563682540818587845 809735543190476403485221)
                    ·
                      rfl

theorem cell23_4730863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 4].length) (baseStart_4730863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730863 prefixEnd_4730863 := by exact prefixLift 4730863
  have htrace : WordTrace (prefixWord ++ tailWord_4730863) baseStart_4730863 baseEnd_4730863 := by
    simpa [prefixWord, tailWord_4730863, baseEnd_4730863] using wordTrace_append hprefix tailTrace_4730863
  have hstable : (prefixWord ++ tailWord_4730863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730863).length < 2 ^ (prefixWord ++ tailWord_4730863).sum := by decide
  have hdescent : baseEnd_4730863 < baseStart_4730863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730870 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_4730870 : Nat := 118140960795 + 4730870 * 2 ^ 59
def prefixEnd_4730870 : Nat := 4983230072969 + 3 ^ 40 * 4730870 * 2
def baseEnd_4730870 : Nat := 2429210223936010683068131

theorem tailTrace_4730870 : CollatzResearch.WordTrace tailWord_4730870 prefixEnd_4730870 2429210223936010683068131 := by
  unfold tailWord_4730870
  simp only [CollatzResearch.WordTrace]
  refine ⟨10784312773179589569716879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 115032669580582288743646709 10784312773179589569716879)
  ·
    refine ⟨16176469159769384354575319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10784312773179589569716879 16176469159769384354575319)
    ·
      refine ⟨24264703739654076531862979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16176469159769384354575319 24264703739654076531862979)
      ·
        refine ⟨36397055609481114797794469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24264703739654076531862979 36397055609481114797794469)
        ·
          refine ⟨6824447926777709024586463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36397055609481114797794469 6824447926777709024586463)
          ·
            refine ⟨10236671890166563536879695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6824447926777709024586463 10236671890166563536879695)
            ·
              refine ⟨15355007835249845305319543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10236671890166563536879695 15355007835249845305319543)
              ·
                refine ⟨23032511752874767957979315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15355007835249845305319543 23032511752874767957979315)
                ·
                  refine ⟨34548767629312151936968973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23032511752874767957979315 34548767629312151936968973)
                  ·
                    refine ⟨12955787860992056976363365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34548767629312151936968973 12955787860992056976363365)
                    ·
                      refine ⟨2429210223936010683068131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12955787860992056976363365 2429210223936010683068131)
                      ·
                        rfl

theorem cell23_4730870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_4730870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730870 prefixEnd_4730870 := by exact prefixLift 4730870
  have htrace : WordTrace (prefixWord ++ tailWord_4730870) baseStart_4730870 baseEnd_4730870 := by
    simpa [prefixWord, tailWord_4730870, baseEnd_4730870] using wordTrace_append hprefix tailTrace_4730870
  have hstable : (prefixWord ++ tailWord_4730870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730870).length < 2 ^ (prefixWord ++ tailWord_4730870).sum := by decide
  have hdescent : baseEnd_4730870 < baseStart_4730870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730873 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 3]
def baseStart_4730873 : Nat := 118140960795 + 4730873 * 2 ^ 59
def prefixEnd_4730873 : Nat := 4983230072969 + 3 ^ 40 * 4730873 * 2
def baseEnd_4730873 : Nat := 2429211764377974171330617

theorem tailTrace_4730873 : CollatzResearch.WordTrace tailWord_4730873 prefixEnd_4730873 2429211764377974171330617 := by
  unfold tailWord_4730873
  simp only [CollatzResearch.WordTrace]
  refine ⟨172549113789862564627829273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115032742526575043085219515 172549113789862564627829273)
  ·
    refine ⟨129411835342396923470871955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172549113789862564627829273 129411835342396923470871955)
    ·
      refine ⟨194117753013595385206307933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129411835342396923470871955 194117753013595385206307933)
      ·
        refine ⟨72794157380098269452365475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194117753013595385206307933 72794157380098269452365475)
        ·
          refine ⟨109191236070147404178548213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72794157380098269452365475 109191236070147404178548213)
          ·
            refine ⟨10236678381576319141738895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109191236070147404178548213 10236678381576319141738895)
            ·
              refine ⟨15355017572364478712608343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10236678381576319141738895 15355017572364478712608343)
              ·
                refine ⟨23032526358546718068912515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15355017572364478712608343 23032526358546718068912515)
                ·
                  refine ⟨34548789537820077103368773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23032526358546718068912515 34548789537820077103368773)
                  ·
                    refine ⟨6477898038341264456881645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34548789537820077103368773 6477898038341264456881645)
                    ·
                      refine ⟨2429211764377974171330617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6477898038341264456881645 2429211764377974171330617)
                      ·
                        rfl

theorem cell23_4730873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_4730873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730873 prefixEnd_4730873 := by exact prefixLift 4730873
  have htrace : WordTrace (prefixWord ++ tailWord_4730873) baseStart_4730873 baseEnd_4730873 := by
    simpa [prefixWord, tailWord_4730873, baseEnd_4730873] using wordTrace_append hprefix tailTrace_4730873
  have hstable : (prefixWord ++ tailWord_4730873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730873).length < 2 ^ (prefixWord ++ tailWord_4730873).sum := by decide
  have hdescent : baseEnd_4730873 < baseStart_4730873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730876 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 8]
def baseStart_4730876 : Nat := 118140960795 + 4730876 * 2 ^ 59
def prefixEnd_4730876 : Nat := 4983230072969 + 3 ^ 40 * 4730876 * 2
def baseEnd_4730876 : Nat := 269912589424437517732567

theorem tailTrace_4730876 : CollatzResearch.WordTrace tailWord_4730876 prefixEnd_4730876 269912589424437517732567 := by
  unfold tailWord_4730876
  simp only [CollatzResearch.WordTrace]
  refine ⟨86274611604425848070094241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115032815472567797426792321 86274611604425848070094241)
  ·
    refine ⟨64705958703319386052570681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86274611604425848070094241 64705958703319386052570681)
    ·
      refine ⟨48529469027489539539428011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64705958703319386052570681 48529469027489539539428011)
      ·
        refine ⟨72794203541234309309142017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48529469027489539539428011 72794203541234309309142017)
        ·
          refine ⟨54595652655925731981856513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72794203541234309309142017 54595652655925731981856513)
          ·
            refine ⟨40946739491944298986392385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54595652655925731981856513 40946739491944298986392385)
            ·
              refine ⟨30710054618958224239794289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40946739491944298986392385 30710054618958224239794289)
              ·
                refine ⟨23032540964218668179845717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30710054618958224239794289 23032540964218668179845717)
                ·
                  refine ⟨269912589424437517732567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23032540964218668179845717 269912589424437517732567)
                  ·
                    rfl

theorem cell23_4730876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_4730876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730876 prefixEnd_4730876 := by exact prefixLift 4730876
  have htrace : WordTrace (prefixWord ++ tailWord_4730876) baseStart_4730876 baseEnd_4730876 := by
    simpa [prefixWord, tailWord_4730876, baseEnd_4730876] using wordTrace_append hprefix tailTrace_4730876
  have hstable : (prefixWord ++ tailWord_4730876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730876).length < 2 ^ (prefixWord ++ tailWord_4730876).sum := by decide
  have hdescent : baseEnd_4730876 < baseStart_4730876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730930 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_4730930 : Nat := 118140960795 + 4730930 * 2 ^ 59
def prefixEnd_4730930 : Nat := 4983230072969 + 3 ^ 40 * 4730930 * 2
def baseEnd_4730930 : Nat := 2429241032775280448317855

theorem tailTrace_4730930 : CollatzResearch.WordTrace tailWord_4730930 prefixEnd_4730930 2429241032775280448317855 := by
  unfold tailWord_4730930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43137798187664015840663561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115034128500437375575102829 43137798187664015840663561)
  ·
    refine ⟨32353348640748011880497671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43137798187664015840663561 32353348640748011880497671)
    ·
      refine ⟨48530022961122017820746507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32353348640748011880497671 48530022961122017820746507)
      ·
        refine ⟨72795034441683026731119761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48530022961122017820746507 72795034441683026731119761)
        ·
          refine ⟨54596275831262270048339821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72795034441683026731119761 54596275831262270048339821)
          ·
            refine ⟨20473603436723351268127433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54596275831262270048339821 20473603436723351268127433)
            ·
              refine ⟨15355202577542513451095575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20473603436723351268127433 15355202577542513451095575)
              ·
                refine ⟨23032803866313770176643363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15355202577542513451095575 23032803866313770176643363)
                ·
                  refine ⟨34549205799470655264965045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23032803866313770176643363 34549205799470655264965045)
                  ·
                    refine ⟨3238988043700373931090473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34549205799470655264965045 3238988043700373931090473)
                    ·
                      refine ⟨2429241032775280448317855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3238988043700373931090473 2429241032775280448317855)
                      ·
                        rfl

theorem cell23_4730930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_4730930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730930 prefixEnd_4730930 := by exact prefixLift 4730930
  have htrace : WordTrace (prefixWord ++ tailWord_4730930) baseStart_4730930 baseEnd_4730930 := by
    simpa [prefixWord, tailWord_4730930, baseEnd_4730930] using wordTrace_append hprefix tailTrace_4730930
  have hstable : (prefixWord ++ tailWord_4730930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730930).length < 2 ^ (prefixWord ++ tailWord_4730930).sum := by decide
  have hdescent : baseEnd_4730930 < baseStart_4730930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730953 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 4, 4]
def baseStart_4730953 : Nat := 118140960795 + 4730953 * 2 ^ 59
def prefixEnd_4730953 : Nat := 4983230072969 + 3 ^ 40 * 4730953 * 2
def baseEnd_4730953 : Nat := 809750947610111286110083

theorem tailTrace_4730953 : CollatzResearch.WordTrace tailWord_4730953 prefixEnd_4730953 809750947610111286110083 := by
  unfold tailWord_4730953
  simp only [CollatzResearch.WordTrace]
  refine ⟨172552031629572738290741513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115034687753048492193827675 172552031629572738290741513)
  ·
    refine ⟨129414023722179553718056135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172552031629572738290741513 129414023722179553718056135)
    ·
      refine ⟨194121035583269330577084203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129414023722179553718056135 194121035583269330577084203)
      ·
        refine ⟨291181553374903995865626305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194121035583269330577084203 291181553374903995865626305)
        ·
          refine ⟨218386165031177996899219729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291181553374903995865626305 218386165031177996899219729)
          ·
            refine ⟨163789623773383497674414797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218386165031177996899219729 163789623773383497674414797)
            ·
              refine ⟨61421108915018811627905549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163789623773383497674414797 61421108915018811627905549)
              ·
                refine ⟨23032915843132054360464581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61421108915018811627905549 23032915843132054360464581)
                ·
                  refine ⟨4318671720587260192587109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23032915843132054360464581 4318671720587260192587109)
                  ·
                    refine ⟨809750947610111286110083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318671720587260192587109 809750947610111286110083)
                    ·
                      rfl

theorem cell23_4730953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 4].length) (baseStart_4730953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730953 prefixEnd_4730953 := by exact prefixLift 4730953
  have htrace : WordTrace (prefixWord ++ tailWord_4730953) baseStart_4730953 baseEnd_4730953 := by
    simpa [prefixWord, tailWord_4730953, baseEnd_4730953] using wordTrace_append hprefix tailTrace_4730953
  have hstable : (prefixWord ++ tailWord_4730953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730953).length < 2 ^ (prefixWord ++ tailWord_4730953).sum := by decide
  have hdescent : baseEnd_4730953 < baseStart_4730953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730970 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_4730970 : Nat := 118140960795 + 4730970 * 2 ^ 59
def prefixEnd_4730970 : Nat := 4983230072969 + 3 ^ 40 * 4730970 * 2
def baseEnd_4730970 : Nat := 809753857333820097272557

theorem tailTrace_4730970 : CollatzResearch.WordTrace tailWord_4730970 prefixEnd_4730970 809753857333820097272557 := by
  unfold tailWord_4730970
  simp only [CollatzResearch.WordTrace]
  refine ⟨43138162917627787548527591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115035101113674100129406909 43138162917627787548527591)
  ·
    refine ⟨64707244376441681322791387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43138162917627787548527591 64707244376441681322791387)
    ·
      refine ⟨97060866564662521984187081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64707244376441681322791387 97060866564662521984187081)
      ·
        refine ⟨72795649923496891488140311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97060866564662521984187081 72795649923496891488140311)
        ·
          refine ⟨109193474885245337232210467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72795649923496891488140311 109193474885245337232210467)
          ·
            refine ⟨163790212327868005848315701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109193474885245337232210467 163790212327868005848315701)
            ·
              refine ⟨15355332405737625548279597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163790212327868005848315701 15355332405737625548279597)
              ·
                refine ⟨5758249652151609580604849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15355332405737625548279597 5758249652151609580604849)
                ·
                  refine ⟨4318687239113707185453637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5758249652151609580604849 4318687239113707185453637)
                  ·
                    refine ⟨809753857333820097272557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4318687239113707185453637 809753857333820097272557)
                    ·
                      rfl

theorem cell23_4730970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_4730970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730970 prefixEnd_4730970 := by exact prefixLift 4730970
  have htrace : WordTrace (prefixWord ++ tailWord_4730970) baseStart_4730970 baseEnd_4730970 := by
    simpa [prefixWord, tailWord_4730970, baseEnd_4730970] using wordTrace_append hprefix tailTrace_4730970
  have hstable : (prefixWord ++ tailWord_4730970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730970).length < 2 ^ (prefixWord ++ tailWord_4730970).sum := by decide
  have hdescent : baseEnd_4730970 < baseStart_4730970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730974 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4730974 : Nat := 118140960795 + 4730974 * 2 ^ 59
def prefixEnd_4730974 : Nat := 4983230072969 + 3 ^ 40 * 4730974 * 2
def baseEnd_4730974 : Nat := 809754541974692758722551

theorem tailTrace_4730974 : CollatzResearch.WordTrace tailWord_4730974 prefixEnd_4730974 809754541974692758722551 := by
  unfold tailWord_4730974
  simp only [CollatzResearch.WordTrace]
  refine ⟨21569099695312082359656997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115035198374997772584837317 21569099695312082359656997)
  ·
    refine ⟨4044206192871015442435687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21569099695312082359656997 4044206192871015442435687)
    ·
      refine ⟨6066309289306523163653531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4044206192871015442435687 6066309289306523163653531)
      ·
        refine ⟨9099463933959784745480297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6066309289306523163653531 9099463933959784745480297)
        ·
          refine ⟨6824597950469838559110223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9099463933959784745480297 6824597950469838559110223)
          ·
            refine ⟨10236896925704757838665335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6824597950469838559110223 10236896925704757838665335)
            ·
              refine ⟨15355345388557136757998003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10236896925704757838665335 15355345388557136757998003)
              ·
                refine ⟨23033018082835705136997005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15355345388557136757998003 23033018082835705136997005)
                ·
                  refine ⟨8637381781063389426373877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23033018082835705136997005 8637381781063389426373877)
                  ·
                    refine ⟨809754541974692758722551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8637381781063389426373877 809754541974692758722551)
                    ·
                      rfl

theorem cell23_4730974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4730974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730974 prefixEnd_4730974 := by exact prefixLift 4730974
  have htrace : WordTrace (prefixWord ++ tailWord_4730974) baseStart_4730974 baseEnd_4730974 := by
    simpa [prefixWord, tailWord_4730974, baseEnd_4730974] using wordTrace_append hprefix tailTrace_4730974
  have hstable : (prefixWord ++ tailWord_4730974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730974).length < 2 ^ (prefixWord ++ tailWord_4730974).sum := by decide
  have hdescent : baseEnd_4730974 < baseStart_4730974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4730990 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4730990 : Nat := 118140960795 + 4730990 * 2 ^ 59
def prefixEnd_4730990 : Nat := 4983230072969 + 3 ^ 40 * 4730990 * 2
def baseEnd_4730990 : Nat := 2429271841614550213567579

theorem tailTrace_4730990 : CollatzResearch.WordTrace tailWord_4730990 prefixEnd_4730990 2429271841614550213567579 := by
  unfold tailWord_4730990
  simp only [CollatzResearch.WordTrace]
  refine ⟨21569172641304836701229803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115035587420292462406558949 21569172641304836701229803)
  ·
    refine ⟨32353758961957255051844705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21569172641304836701229803 32353758961957255051844705)
    ·
      refine ⟨24265319221467941288883529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32353758961957255051844705 24265319221467941288883529)
      ·
        refine ⟨18198989416100955966662647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24265319221467941288883529 18198989416100955966662647)
        ·
          refine ⟨27298484124151433949993971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18198989416100955966662647 27298484124151433949993971)
          ·
            refine ⟨40947726186227150924990957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27298484124151433949993971 40947726186227150924990957)
            ·
              refine ⟨15355397319835181596871609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40947726186227150924990957 15355397319835181596871609)
              ·
                refine ⟨11516547989876386197653707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15355397319835181596871609 11516547989876386197653707)
                ·
                  refine ⟨17274821984814579296480561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11516547989876386197653707 17274821984814579296480561)
                  ·
                    refine ⟨12956116488610934472360421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17274821984814579296480561 12956116488610934472360421)
                    ·
                      refine ⟨2429271841614550213567579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12956116488610934472360421 2429271841614550213567579)
                      ·
                        rfl

theorem cell23_4730990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4730990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4730990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4730990 prefixEnd_4730990 := by exact prefixLift 4730990
  have htrace : WordTrace (prefixWord ++ tailWord_4730990) baseStart_4730990 baseEnd_4730990 := by
    simpa [prefixWord, tailWord_4730990, baseEnd_4730990] using wordTrace_append hprefix tailTrace_4730990
  have hstable : (prefixWord ++ tailWord_4730990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4730990).length < 2 ^ (prefixWord ++ tailWord_4730990).sum := by decide
  have hdescent : baseEnd_4730990 < baseStart_4730990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4730990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731011 : List Nat := [1, 1, 1, 3, 3, 3, 4, 2, 1, 2, 2]
def baseStart_4731011 : Nat := 118140960795 + 4731011 * 2 ^ 59
def prefixEnd_4731011 : Nat := 4983230072969 + 3 ^ 40 * 4731011 * 2
def baseEnd_4731011 : Nat := 2429282624708294631404983

theorem tailTrace_4731011 : CollatzResearch.WordTrace tailWord_4731011 prefixEnd_4731011 2429282624708294631404983 := by
  unfold tailWord_4731011
  simp only [CollatzResearch.WordTrace]
  refine ⟨172554147063362614196352887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115036098042241742797568591 172554147063362614196352887)
  ·
    refine ⟨258831220595043921294529331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172554147063362614196352887 258831220595043921294529331)
    ·
      refine ⟨388246830892565881941793997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258831220595043921294529331 388246830892565881941793997)
      ·
        refine ⟨145592561584712205728172749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 388246830892565881941793997 145592561584712205728172749)
        ·
          refine ⟨54597210594267077148064781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145592561584712205728172749 54597210594267077148064781)
          ·
            refine ⟨20473953972850153930524293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54597210594267077148064781 20473953972850153930524293)
            ·
              refine ⟨3838866369909403861973305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20473953972850153930524293 3838866369909403861973305)
              ·
                refine ⟨2879149777432052896479979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3838866369909403861973305 2879149777432052896479979)
                ·
                  refine ⟨4318724666148079344719969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2879149777432052896479979 4318724666148079344719969)
                  ·
                    refine ⟨3239043499611059508539977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4318724666148079344719969 3239043499611059508539977)
                    ·
                      refine ⟨2429282624708294631404983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239043499611059508539977 2429282624708294631404983)
                      ·
                        rfl

theorem cell23_4731011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 2, 2].length) (baseStart_4731011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731011 prefixEnd_4731011 := by exact prefixLift 4731011
  have htrace : WordTrace (prefixWord ++ tailWord_4731011) baseStart_4731011 baseEnd_4731011 := by
    simpa [prefixWord, tailWord_4731011, baseEnd_4731011] using wordTrace_append hprefix tailTrace_4731011
  have hstable : (prefixWord ++ tailWord_4731011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731011).length < 2 ^ (prefixWord ++ tailWord_4731011).sum := by decide
  have hdescent : baseEnd_4731011 < baseStart_4731011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731013 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_4731013 : Nat := 118140960795 + 4731013 * 2 ^ 59
def prefixEnd_4731013 : Nat := 4983230072969 + 3 ^ 40 * 4731013 * 2
def baseEnd_4731013 : Nat := 809761217223201207859991

theorem tailTrace_4731013 : CollatzResearch.WordTrace tailWord_4731013 prefixEnd_4731013 809761217223201207859991 := by
  unfold tailWord_4731013
  simp only [CollatzResearch.WordTrace]
  refine ⟨172554220009355368537925693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115036146672903579025283795 172554220009355368537925693)
  ·
    refine ⟨64707832503508263201722135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172554220009355368537925693 64707832503508263201722135)
    ·
      refine ⟨97061748755262394802583203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64707832503508263201722135 97061748755262394802583203)
      ·
        refine ⟨145592623132893592203874805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97061748755262394802583203 145592623132893592203874805)
        ·
          refine ⟨13649308418708774269113263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145592623132893592203874805 13649308418708774269113263)
          ·
            refine ⟨20473962628063161403669895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13649308418708774269113263 20473962628063161403669895)
            ·
              refine ⟨30710943942094742105504843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20473962628063161403669895 30710943942094742105504843)
              ·
                refine ⟨46066415913142113158257265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30710943942094742105504843 46066415913142113158257265)
                ·
                  refine ⟨34549811934856584868692949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46066415913142113158257265 34549811934856584868692949)
                  ·
                    refine ⟨809761217223201207859991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34549811934856584868692949 809761217223201207859991)
                    ·
                      rfl

theorem cell23_4731013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_4731013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731013 prefixEnd_4731013 := by exact prefixLift 4731013
  have htrace : WordTrace (prefixWord ++ tailWord_4731013) baseStart_4731013 baseEnd_4731013 := by
    simpa [prefixWord, tailWord_4731013, baseEnd_4731013] using wordTrace_append hprefix tailTrace_4731013
  have hstable : (prefixWord ++ tailWord_4731013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731013).length < 2 ^ (prefixWord ++ tailWord_4731013).sum := by decide
  have hdescent : baseEnd_4731013 < baseStart_4731013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731037 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_4731037 : Nat := 118140960795 + 4731037 * 2 ^ 59
def prefixEnd_4731037 : Nat := 4983230072969 + 3 ^ 40 * 4731037 * 2
def baseEnd_4731037 : Nat := 2429295975205311529679863

theorem tailTrace_4731037 : CollatzResearch.WordTrace tailWord_4731037 prefixEnd_4731037 2429295975205311529679863 := by
  unfold tailWord_4731037
  simp only [CollatzResearch.WordTrace]
  refine ⟨172555095361268420636799365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115036730240845613757866243 172555095361268420636799365)
  ·
    refine ⟨32354080380237828869399881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172555095361268420636799365 32354080380237828869399881)
    ·
      refine ⟨24265560285178371652049911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32354080380237828869399881 24265560285178371652049911)
      ·
        refine ⟨36398340427767557478074867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24265560285178371652049911 36398340427767557478074867)
        ·
          refine ⟨54597510641651336217112301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36398340427767557478074867 54597510641651336217112301)
          ·
            refine ⟨20474066490619251081417113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54597510641651336217112301 20474066490619251081417113)
            ·
              refine ⟨15355549867964438311062835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20474066490619251081417113 15355549867964438311062835)
              ·
                refine ⟨23033324801946657466594253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15355549867964438311062835 23033324801946657466594253)
                ·
                  refine ⟨8637496800729996549972845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23033324801946657466594253 8637496800729996549972845)
                  ·
                    refine ⟨3239061300273748706239817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8637496800729996549972845 3239061300273748706239817)
                    ·
                      refine ⟨2429295975205311529679863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239061300273748706239817 2429295975205311529679863)
                      ·
                        rfl

theorem cell23_4731037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_4731037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731037 prefixEnd_4731037 := by exact prefixLift 4731037
  have htrace : WordTrace (prefixWord ++ tailWord_4731037) baseStart_4731037 baseEnd_4731037 := by
    simpa [prefixWord, tailWord_4731037, baseEnd_4731037] using wordTrace_append hprefix tailTrace_4731037
  have hstable : (prefixWord ++ tailWord_4731037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731037).length < 2 ^ (prefixWord ++ tailWord_4731037).sum := by decide
  have hdescent : baseEnd_4731037 < baseStart_4731037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731067 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 4, 2, 2]
def baseStart_4731067 : Nat := 118140960795 + 4731067 * 2 ^ 59
def prefixEnd_4731067 : Nat := 4983230072969 + 3 ^ 40 * 4731067 * 2
def baseEnd_4731067 : Nat := 2429311379624946412304725

theorem tailTrace_4731067 : CollatzResearch.WordTrace tailWord_4731067 prefixEnd_4731067 2429311379624946412304725 := by
  unfold tailWord_4731067
  simp only [CollatzResearch.WordTrace]
  refine ⟨172556189551159735760391455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115037459700773157173594303 172556189551159735760391455)
  ·
    refine ⟨258834284326739603640587183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172556189551159735760391455 258834284326739603640587183)
    ·
      refine ⟨388251426490109405460880775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258834284326739603640587183 388251426490109405460880775)
      ·
        refine ⟨582377139735164108191321163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388251426490109405460880775 582377139735164108191321163)
        ·
          refine ⟨873565709602746162286981745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582377139735164108191321163 873565709602746162286981745)
          ·
            refine ⟨655174282202059621715236309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 873565709602746162286981745 655174282202059621715236309)
            ·
              refine ⟨15355647239110772383950851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 655174282202059621715236309 15355647239110772383950851)
              ·
                refine ⟨23033470858666158575926277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15355647239110772383950851 23033470858666158575926277)
                ·
                  refine ⟨4318775785999904732986177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23033470858666158575926277 4318775785999904732986177)
                  ·
                    refine ⟨3239081839499928549739633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4318775785999904732986177 3239081839499928549739633)
                    ·
                      refine ⟨2429311379624946412304725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239081839499928549739633 2429311379624946412304725)
                      ·
                        rfl

theorem cell23_4731067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 2, 2].length) (baseStart_4731067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731067 prefixEnd_4731067 := by exact prefixLift 4731067
  have htrace : WordTrace (prefixWord ++ tailWord_4731067) baseStart_4731067 baseEnd_4731067 := by
    simpa [prefixWord, tailWord_4731067, baseEnd_4731067] using wordTrace_append hprefix tailTrace_4731067
  have hstable : (prefixWord ++ tailWord_4731067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731067).length < 2 ^ (prefixWord ++ tailWord_4731067).sum := by decide
  have hdescent : baseEnd_4731067 < baseStart_4731067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731090 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 7]
def baseStart_4731090 : Nat := 118140960795 + 4731090 * 2 ^ 59
def prefixEnd_4731090 : Nat := 4983230072969 + 3 ^ 40 * 4731090 * 2
def baseEnd_4731090 : Nat := 269924798853333313590791

theorem tailTrace_4731090 : CollatzResearch.WordTrace tailWord_4731090 prefixEnd_4731090 269924798853333313590791 := by
  unfold tailWord_4731090
  simp only [CollatzResearch.WordTrace]
  refine ⟨43139257107519102672119681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115038018953384273792319149 43139257107519102672119681)
  ·
    refine ⟨32354442830639327004089761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43139257107519102672119681 32354442830639327004089761)
    ·
      refine ⟨24265832122979495253067321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32354442830639327004089761 24265832122979495253067321)
      ·
        refine ⟨18199374092234621439800491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24265832122979495253067321 18199374092234621439800491)
        ·
          refine ⟨27299061138351932159700737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18199374092234621439800491 27299061138351932159700737)
          ·
            refine ⟨20474295853763949119775553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27299061138351932159700737 20474295853763949119775553)
            ·
              refine ⟨15355721890322961839831665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20474295853763949119775553 15355721890322961839831665)
              ·
                refine ⟨11516791417742221379873749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15355721890322961839831665 11516791417742221379873749)
                ·
                  refine ⟨269924798853333313590791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11516791417742221379873749 269924798853333313590791)
                  ·
                    rfl

theorem cell23_4731090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_4731090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731090 prefixEnd_4731090 := by exact prefixLift 4731090
  have htrace : WordTrace (prefixWord ++ tailWord_4731090) baseStart_4731090 baseEnd_4731090 := by
    simpa [prefixWord, tailWord_4731090, baseEnd_4731090] using wordTrace_append hprefix tailTrace_4731090
  have hstable : (prefixWord ++ tailWord_4731090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731090).length < 2 ^ (prefixWord ++ tailWord_4731090).sum := by decide
  have hdescent : baseEnd_4731090 < baseStart_4731090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731113 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_4731113 : Nat := 118140960795 + 4731113 * 2 ^ 59
def prefixEnd_4731113 : Nat := 4983230072969 + 3 ^ 40 * 4731113 * 2
def baseEnd_4731113 : Nat := 2429334999735053232329513

theorem tailTrace_4731113 : CollatzResearch.WordTrace tailWord_4731113 prefixEnd_4731113 2429334999735053232329513 := by
  unfold tailWord_4731113
  simp only [CollatzResearch.WordTrace]
  refine ⟨172557867308993085616565993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115038578205995390411043995 172557867308993085616565993)
  ·
    refine ⟨129418400481744814212424495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172557867308993085616565993 129418400481744814212424495)
    ·
      refine ⟨194127600722617221318636743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129418400481744814212424495 194127600722617221318636743)
      ·
        refine ⟨291191401083925831977955115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194127600722617221318636743 291191401083925831977955115)
        ·
          refine ⟨436787101625888747966932673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291191401083925831977955115 436787101625888747966932673)
          ·
            refine ⟨327590326219416560975199505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436787101625888747966932673 327590326219416560975199505)
            ·
              refine ⟨245692744664562420731399629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327590326219416560975199505 245692744664562420731399629)
              ·
                refine ⟨92134779249210907774274861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245692744664562420731399629 92134779249210907774274861)
                ·
                  refine ⟨34550542218454090415353073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92134779249210907774274861 34550542218454090415353073)
                  ·
                    refine ⟨25912906663840567811514805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34550542218454090415353073 25912906663840567811514805)
                    ·
                      refine ⟨2429334999735053232329513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25912906663840567811514805 2429334999735053232329513)
                      ·
                        rfl

theorem cell23_4731113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_4731113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731113 prefixEnd_4731113 := by exact prefixLift 4731113
  have htrace : WordTrace (prefixWord ++ tailWord_4731113) baseStart_4731113 baseEnd_4731113 := by
    simpa [prefixWord, tailWord_4731113, baseEnd_4731113] using wordTrace_append hprefix tailTrace_4731113
  have hstable : (prefixWord ++ tailWord_4731113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731113).length < 2 ^ (prefixWord ++ tailWord_4731113).sum := by decide
  have hdescent : baseEnd_4731113 < baseStart_4731113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731130 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_4731130 : Nat := 118140960795 + 4731130 * 2 ^ 59
def prefixEnd_4731130 : Nat := 4983230072969 + 3 ^ 40 * 4731130 * 2
def baseEnd_4731130 : Nat := 2429343728906179665816935

theorem tailTrace_4731130 : CollatzResearch.WordTrace tailWord_4731130 prefixEnd_4731130 2429343728906179665816935 := by
  unfold tailWord_4731130
  simp only [CollatzResearch.WordTrace]
  refine ⟨43139621837482874379983711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115038991566620998346623229 43139621837482874379983711)
  ·
    refine ⟨64709432756224311569975567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43139621837482874379983711 64709432756224311569975567)
    ·
      refine ⟨97064149134336467354963351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64709432756224311569975567 97064149134336467354963351)
      ·
        refine ⟨145596223701504701032445027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97064149134336467354963351 145596223701504701032445027)
        ·
          refine ⟨218394335552257051548667541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145596223701504701032445027 218394335552257051548667541)
          ·
            refine ⟨10237234479012049291343791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 218394335552257051548667541 10237234479012049291343791)
            ·
              refine ⟨15355851718518073937015687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10237234479012049291343791 15355851718518073937015687)
              ·
                refine ⟨23033777577777110905523531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15355851718518073937015687 23033777577777110905523531)
                ·
                  refine ⟨34550666366665666358285297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23033777577777110905523531 34550666366665666358285297)
                  ·
                    refine ⟨25912999774999249768713973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34550666366665666358285297 25912999774999249768713973)
                    ·
                      refine ⟨2429343728906179665816935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25912999774999249768713973 2429343728906179665816935)
                      ·
                        rfl

theorem cell23_4731130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_4731130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731130 prefixEnd_4731130 := by exact prefixLift 4731130
  have htrace : WordTrace (prefixWord ++ tailWord_4731130) baseStart_4731130 baseEnd_4731130 := by
    simpa [prefixWord, tailWord_4731130, baseEnd_4731130] using wordTrace_append hprefix tailTrace_4731130
  have hstable : (prefixWord ++ tailWord_4731130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731130).length < 2 ^ (prefixWord ++ tailWord_4731130).sum := by decide
  have hdescent : baseEnd_4731130 < baseStart_4731130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731163 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 10]
def baseStart_4731163 : Nat := 118140960795 + 4731163 * 2 ^ 59
def prefixEnd_4731163 : Nat := 4983230072969 + 3 ^ 40 * 4731163 * 2
def baseEnd_4731163 : Nat := 269928963751975337411587

theorem tailTrace_4731163 : CollatzResearch.WordTrace tailWord_4731163 prefixEnd_4731163 269928963751975337411587 := by
  unfold tailWord_4731163
  simp only [CollatzResearch.WordTrace]
  refine ⟨172559690958811944155886143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115039793972541296103924095 172559690958811944155886143)
  ·
    refine ⟨258839536438217916233829215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172559690958811944155886143 258839536438217916233829215)
    ·
      refine ⟨388259304657326874350743823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258839536438217916233829215 388259304657326874350743823)
      ·
        refine ⟨582388956985990311526115735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388259304657326874350743823 582388956985990311526115735)
        ·
          refine ⟨873583435478985467289173603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582388956985990311526115735 873583435478985467289173603)
          ·
            refine ⟨1310375153218478200933760405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873583435478985467289173603 1310375153218478200933760405)
            ·
              refine ⟨61423835307116165668770019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1310375153218478200933760405 61423835307116165668770019)
              ·
                refine ⟨92135752960674248503155029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61423835307116165668770019 92135752960674248503155029)
                ·
                  refine ⟨269928963751975337411587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 92135752960674248503155029 269928963751975337411587)
                  ·
                    rfl

theorem cell23_4731163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 10].length) (baseStart_4731163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731163 prefixEnd_4731163 := by exact prefixLift 4731163
  have htrace : WordTrace (prefixWord ++ tailWord_4731163) baseStart_4731163 baseEnd_4731163 := by
    simpa [prefixWord, tailWord_4731163, baseEnd_4731163] using wordTrace_append hprefix tailTrace_4731163
  have hstable : (prefixWord ++ tailWord_4731163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731163).length < 2 ^ (prefixWord ++ tailWord_4731163).sum := by decide
  have hdescent : baseEnd_4731163 < baseStart_4731163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731175 : List Nat := [1, 1, 8, 1, 1, 2, 2, 2, 5]
def baseStart_4731175 : Nat := 118140960795 + 4731175 * 2 ^ 59
def prefixEnd_4731175 : Nat := 4983230072969 + 3 ^ 40 * 4731175 * 2
def baseEnd_4731175 : Nat := 269929648392847998861581

theorem tailTrace_4731175 : CollatzResearch.WordTrace tailWord_4731175 prefixEnd_4731175 269929648392847998861581 := by
  unfold tailWord_4731175
  simp only [CollatzResearch.WordTrace]
  refine ⟨172560128634768470205322979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115040085756512313470215319 172560128634768470205322979)
  ·
    refine ⟨258840192952152705307984469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172560128634768470205322979 258840192952152705307984469)
    ·
      refine ⟨3033283511158039515327943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 258840192952152705307984469 3033283511158039515327943)
      ·
        refine ⟨4549925266737059272991915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3033283511158039515327943 4549925266737059272991915)
        ·
          refine ⟨6824887900105588909487873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4549925266737059272991915 6824887900105588909487873)
          ·
            refine ⟨5118665925079191682115905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6824887900105588909487873 5118665925079191682115905)
            ·
              refine ⟨3838999443809393761586929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5118665925079191682115905 3838999443809393761586929)
              ·
                refine ⟨2879249582857045321190197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3838999443809393761586929 2879249582857045321190197)
                ·
                  refine ⟨269929648392847998861581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2879249582857045321190197 269929648392847998861581)
                  ·
                    rfl

theorem cell23_4731175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 5].length) (baseStart_4731175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731175 prefixEnd_4731175 := by exact prefixLift 4731175
  have htrace : WordTrace (prefixWord ++ tailWord_4731175) baseStart_4731175 baseEnd_4731175 := by
    simpa [prefixWord, tailWord_4731175, baseEnd_4731175] using wordTrace_append hprefix tailTrace_4731175
  have hstable : (prefixWord ++ tailWord_4731175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731175).length < 2 ^ (prefixWord ++ tailWord_4731175).sum := by decide
  have hdescent : baseEnd_4731175 < baseStart_4731175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731180 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 6]
def baseStart_4731180 : Nat := 118140960795 + 4731180 * 2 ^ 59
def prefixEnd_4731180 : Nat := 4983230072969 + 3 ^ 40 * 4731180 * 2
def baseEnd_4731180 : Nat := 269929933659878274465745

theorem tailTrace_4731180 : CollatzResearch.WordTrace tailWord_4731180 prefixEnd_4731180 269929933659878274465745 := by
  unfold tailWord_4731180
  simp only [CollatzResearch.WordTrace]
  refine ⟨86280155499875178029627497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115040207333166904039503329 86280155499875178029627497)
  ·
    refine ⟨64710116624906383522220623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86280155499875178029627497 64710116624906383522220623)
    ·
      refine ⟨97065174937359575283330935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64710116624906383522220623 97065174937359575283330935)
      ·
        refine ⟨145597762406039362924996403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97065174937359575283330935 145597762406039362924996403)
        ·
          refine ⟨218396643609059044387494605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145597762406039362924996403 218396643609059044387494605)
          ·
            refine ⟨81898741353397141645310477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218396643609059044387494605 81898741353397141645310477)
            ·
              refine ⟨30712028007523928116991429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81898741353397141645310477 30712028007523928116991429)
              ·
                refine ⟨5758505251410736521935893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30712028007523928116991429 5758505251410736521935893)
                ·
                  refine ⟨269929933659878274465745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5758505251410736521935893 269929933659878274465745)
                  ·
                    rfl

theorem cell23_4731180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_4731180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731180 prefixEnd_4731180 := by exact prefixLift 4731180
  have htrace : WordTrace (prefixWord ++ tailWord_4731180) baseStart_4731180 baseEnd_4731180 := by
    simpa [prefixWord, tailWord_4731180, baseEnd_4731180] using wordTrace_append hprefix tailTrace_4731180
  have hstable : (prefixWord ++ tailWord_4731180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731180).length < 2 ^ (prefixWord ++ tailWord_4731180).sum := by decide
  have hdescent : baseEnd_4731180 < baseStart_4731180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731294 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4731294 : Nat := 118140960795 + 4731294 * 2 ^ 59
def prefixEnd_4731294 : Nat := 4983230072969 + 3 ^ 40 * 4731294 * 2
def baseEnd_4731294 : Nat := 2429427939733517024166181

theorem tailTrace_4731294 : CollatzResearch.WordTrace tailWord_4731294 prefixEnd_4731294 2429427939733517024166181 := by
  unfold tailWord_4731294
  simp only [CollatzResearch.WordTrace]
  refine ⟨21570558615167169191113117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115042979280891569019269957 21570558615167169191113117)
  ·
    refine ⟨8088959480687688446667419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21570558615167169191113117 8088959480687688446667419)
    ·
      refine ⟨12133439221031532670001129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8088959480687688446667419 12133439221031532670001129)
      ·
        refine ⟨9100079415773649502500847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12133439221031532670001129 9100079415773649502500847)
        ·
          refine ⟨13650119123660474253751271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9100079415773649502500847 13650119123660474253751271)
          ·
            refine ⟨20475178685490711380626907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13650119123660474253751271 20475178685490711380626907)
            ·
              refine ⟨30712768028236067070940361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20475178685490711380626907 30712768028236067070940361)
              ·
                refine ⟨23034576021177050303205271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30712768028236067070940361 23034576021177050303205271)
                ·
                  refine ⟨34551864031765575454807907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23034576021177050303205271 34551864031765575454807907)
                  ·
                    refine ⟨51827796047648363182211861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34551864031765575454807907 51827796047648363182211861)
                    ·
                      refine ⟨2429427939733517024166181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51827796047648363182211861 2429427939733517024166181)
                      ·
                        rfl

theorem cell23_4731294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4731294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731294 prefixEnd_4731294 := by exact prefixLift 4731294
  have htrace : WordTrace (prefixWord ++ tailWord_4731294) baseStart_4731294 baseEnd_4731294 := by
    simpa [prefixWord, tailWord_4731294, baseEnd_4731294] using wordTrace_append hprefix tailTrace_4731294
  have hstable : (prefixWord ++ tailWord_4731294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731294).length < 2 ^ (prefixWord ++ tailWord_4731294).sum := by decide
  have hdescent : baseEnd_4731294 < baseStart_4731294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731304 : List Nat := [2, 1, 6, 1, 1, 2, 2, 8]
def baseStart_4731304 : Nat := 118140960795 + 4731304 * 2 ^ 59
def prefixEnd_4731304 : Nat := 4983230072969 + 3 ^ 40 * 4731304 * 2
def baseEnd_4731304 : Nat := 89979002760743036483005

theorem tailTrace_4731304 : CollatzResearch.WordTrace tailWord_4731304 prefixEnd_4731304 89979002760743036483005 := by
  unfold tailWord_4731304
  simp only [CollatzResearch.WordTrace]
  refine ⟨86282416825650562618384483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115043222434200750157845977 86282416825650562618384483)
  ·
    refine ⟨129423625238475843927576725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86282416825650562618384483 129423625238475843927576725)
    ·
      refine ⟨6066732433053555184105159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 129423625238475843927576725 6066732433053555184105159)
      ·
        refine ⟨9100098649580332776157739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6066732433053555184105159 9100098649580332776157739)
        ·
          refine ⟨13650147974370499164236609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9100098649580332776157739 13650147974370499164236609)
          ·
            refine ⟨10237610980777874373177457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13650147974370499164236609 10237610980777874373177457)
            ·
              refine ⟨7678208235583405779883093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10237610980777874373177457 7678208235583405779883093)
              ·
                refine ⟨89979002760743036483005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7678208235583405779883093 89979002760743036483005)
                ·
                  rfl

theorem cell23_4731304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 8].length) (baseStart_4731304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731304 prefixEnd_4731304 := by exact prefixLift 4731304
  have htrace : WordTrace (prefixWord ++ tailWord_4731304) baseStart_4731304 baseEnd_4731304 := by
    simpa [prefixWord, tailWord_4731304, baseEnd_4731304] using wordTrace_append hprefix tailTrace_4731304
  have hstable : (prefixWord ++ tailWord_4731304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731304).length < 2 ^ (prefixWord ++ tailWord_4731304).sum := by decide
  have hdescent : baseEnd_4731304 < baseStart_4731304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731320 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_4731320 : Nat := 118140960795 + 4731320 * 2 ^ 59
def prefixEnd_4731320 : Nat := 4983230072969 + 3 ^ 40 * 4731320 * 2
def baseEnd_4731320 : Nat := 2429441290230533922441061

theorem tailTrace_4731320 : CollatzResearch.WordTrace tailWord_4731320 prefixEnd_4731320 2429441290230533922441061 := by
  unfold tailWord_4731320
  simp only [CollatzResearch.WordTrace]
  refine ⟨86282708609621579984675707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115043611479495439979567609 86282708609621579984675707)
  ·
    refine ⟨129424062914432369977013561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86282708609621579984675707 129424062914432369977013561)
    ·
      refine ⟨97068047185824277482760171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129424062914432369977013561 97068047185824277482760171)
      ·
        refine ⟨145602070778736416224140257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97068047185824277482760171 145602070778736416224140257)
        ·
          refine ⟨109201553084052312168105193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145602070778736416224140257 109201553084052312168105193)
          ·
            refine ⟨81901164813039234126078895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109201553084052312168105193 81901164813039234126078895)
            ·
              refine ⟨122851747219558851189118343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81901164813039234126078895 122851747219558851189118343)
              ·
                refine ⟨184277620829338276783677515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122851747219558851189118343 184277620829338276783677515)
                ·
                  refine ⟨276416431244007415175516273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184277620829338276783677515 276416431244007415175516273)
                  ·
                    refine ⟨207312323433005561381637205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 276416431244007415175516273 207312323433005561381637205)
                    ·
                      refine ⟨2429441290230533922441061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 207312323433005561381637205 2429441290230533922441061)
                      ·
                        rfl

theorem cell23_4731320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_4731320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731320 prefixEnd_4731320 := by exact prefixLift 4731320
  have htrace : WordTrace (prefixWord ++ tailWord_4731320) baseStart_4731320 baseEnd_4731320 := by
    simpa [prefixWord, tailWord_4731320, baseEnd_4731320] using wordTrace_append hprefix tailTrace_4731320
  have hstable : (prefixWord ++ tailWord_4731320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731320).length < 2 ^ (prefixWord ++ tailWord_4731320).sum := by decide
  have hdescent : baseEnd_4731320 < baseStart_4731320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731348 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_4731348 : Nat := 118140960795 + 4731348 * 2 ^ 59
def prefixEnd_4731348 : Nat := 4983230072969 + 3 ^ 40 * 4731348 * 2
def baseEnd_4731348 : Nat := 2429455667688859812890933

theorem tailTrace_4731348 : CollatzResearch.WordTrace tailWord_4731348 prefixEnd_4731348 2429455667688859812890933 := by
  unfold tailWord_4731348
  simp only [CollatzResearch.WordTrace]
  refine ⟨86283219231570860375685349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115044292308761147167580465 86283219231570860375685349)
  ·
    refine ⟨16178103605919536320441003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86283219231570860375685349 16178103605919536320441003)
    ·
      refine ⟨24267155408879304480661505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16178103605919536320441003 24267155408879304480661505)
      ·
        refine ⟨18200366556659478360496129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24267155408879304480661505 18200366556659478360496129)
        ·
          refine ⟨13650274917494608770372097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18200366556659478360496129 13650274917494608770372097)
          ·
            refine ⟨10237706188120956577779073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13650274917494608770372097 10237706188120956577779073)
            ·
              refine ⟨7678279641090717433334305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10237706188120956577779073 7678279641090717433334305)
              ·
                refine ⟨5758709730818038075000729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7678279641090717433334305 5758709730818038075000729)
                ·
                  refine ⟨4319032298113528556250547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5758709730818038075000729 4319032298113528556250547)
                  ·
                    refine ⟨6478548447170292834375821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4319032298113528556250547 6478548447170292834375821)
                    ·
                      refine ⟨2429455667688859812890933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6478548447170292834375821 2429455667688859812890933)
                      ·
                        rfl

theorem cell23_4731348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_4731348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731348 prefixEnd_4731348 := by exact prefixLift 4731348
  have htrace : WordTrace (prefixWord ++ tailWord_4731348) baseStart_4731348 baseEnd_4731348 := by
    simpa [prefixWord, tailWord_4731348, baseEnd_4731348] using wordTrace_append hprefix tailTrace_4731348
  have hstable : (prefixWord ++ tailWord_4731348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731348).length < 2 ^ (prefixWord ++ tailWord_4731348).sum := by decide
  have hdescent : baseEnd_4731348 < baseStart_4731348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731354 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2]
def baseStart_4731354 : Nat := 118140960795 + 4731354 * 2 ^ 59
def prefixEnd_4731354 : Nat := 4983230072969 + 3 ^ 40 * 4731354 * 2
def baseEnd_4731354 : Nat := 2429458748572786789415905

theorem tailTrace_4731354 : CollatzResearch.WordTrace tailWord_4731354 prefixEnd_4731354 2429458748572786789415905 := by
  unfold tailWord_4731354
  simp only [CollatzResearch.WordTrace]
  refine ⟨43141664325279995944022279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115044438200746655850726077 43141664325279995944022279)
  ·
    refine ⟨64712496487919993916033419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43141664325279995944022279 64712496487919993916033419)
    ·
      refine ⟨97068744731879990874050129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64712496487919993916033419 97068744731879990874050129)
      ·
        refine ⟨72801558548909993155537597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97068744731879990874050129 72801558548909993155537597)
        ·
          refine ⟨27300584455841247433326599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72801558548909993155537597 27300584455841247433326599)
          ·
            refine ⟨40950876683761871149989899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27300584455841247433326599 40950876683761871149989899)
            ·
              refine ⟨61426315025642806724984849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40950876683761871149989899 61426315025642806724984849)
              ·
                refine ⟨46069736269232105043738637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61426315025642806724984849 46069736269232105043738637)
                ·
                  refine ⟨17276151100962039391401989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46069736269232105043738637 17276151100962039391401989)
                  ·
                    refine ⟨3239278331430382385887873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17276151100962039391401989 3239278331430382385887873)
                    ·
                      refine ⟨2429458748572786789415905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239278331430382385887873 2429458748572786789415905)
                      ·
                        rfl

theorem cell23_4731354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_4731354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731354 prefixEnd_4731354 := by exact prefixLift 4731354
  have htrace : WordTrace (prefixWord ++ tailWord_4731354) baseStart_4731354 baseEnd_4731354 := by
    simpa [prefixWord, tailWord_4731354, baseEnd_4731354] using wordTrace_append hprefix tailTrace_4731354
  have hstable : (prefixWord ++ tailWord_4731354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731354).length < 2 ^ (prefixWord ++ tailWord_4731354).sum := by decide
  have hdescent : baseEnd_4731354 < baseStart_4731354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731371 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 2, 2, 2]
def baseStart_4731371 : Nat := 118140960795 + 4731371 * 2 ^ 59
def prefixEnd_4731371 : Nat := 4983230072969 + 3 ^ 40 * 4731371 * 2
def baseEnd_4731371 : Nat := 2429467477743913222903327

theorem tailTrace_4731371 : CollatzResearch.WordTrace tailWord_4731371 prefixEnd_4731371 2429467477743913222903327 := by
  unfold tailWord_4731371
  simp only [CollatzResearch.WordTrace]
  refine ⟨172567277342058395679457967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115044851561372263786305311 172567277342058395679457967)
  ·
    refine ⟨258850916013087593519186951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172567277342058395679457967 258850916013087593519186951)
    ·
      refine ⟨388276374019631390278780427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258850916013087593519186951 388276374019631390278780427)
      ·
        refine ⟨582414561029447085418170641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388276374019631390278780427 582414561029447085418170641)
        ·
          refine ⟨436810920772085314063627981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582414561029447085418170641 436810920772085314063627981)
          ·
            refine ⟨163804095289531992773860493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 436810920772085314063627981 163804095289531992773860493)
            ·
              refine ⟨61426535733574497290197685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163804095289531992773860493 61426535733574497290197685)
              ·
                refine ⟨5758737725022609120956033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61426535733574497290197685 5758737725022609120956033)
                ·
                  refine ⟨4319053293766956840717025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5758737725022609120956033 4319053293766956840717025)
                  ·
                    refine ⟨3239289970325217630537769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4319053293766956840717025 3239289970325217630537769)
                    ·
                      refine ⟨2429467477743913222903327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239289970325217630537769 2429467477743913222903327)
                      ·
                        rfl

theorem cell23_4731371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 2, 2].length) (baseStart_4731371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731371 prefixEnd_4731371 := by exact prefixLift 4731371
  have htrace : WordTrace (prefixWord ++ tailWord_4731371) baseStart_4731371 baseEnd_4731371 := by
    simpa [prefixWord, tailWord_4731371, baseEnd_4731371] using wordTrace_append hprefix tailTrace_4731371
  have hstable : (prefixWord ++ tailWord_4731371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731371).length < 2 ^ (prefixWord ++ tailWord_4731371).sum := by decide
  have hdescent : baseEnd_4731371 < baseStart_4731371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731377 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 7]
def baseStart_4731377 : Nat := 118140960795 + 4731377 * 2 ^ 59
def prefixEnd_4731377 : Nat := 4983230072969 + 3 ^ 40 * 4731377 * 2
def baseEnd_4731377 : Nat := 269941173180871133269811

theorem tailTrace_4731377 : CollatzResearch.WordTrace tailWord_4731377 prefixEnd_4731377 269941173180871133269811 := by
  unfold tailWord_4731377
  simp only [CollatzResearch.WordTrace]
  refine ⟨172567496180036658704176385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115044997453357772469450923 172567496180036658704176385)
  ·
    refine ⟨129425622135027494028132289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172567496180036658704176385 129425622135027494028132289)
    ·
      refine ⟨97069216601270620521099217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129425622135027494028132289 97069216601270620521099217)
      ·
        refine ⟨72801912450952965390824413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97069216601270620521099217 72801912450952965390824413)
        ·
          refine ⟨27300717169107362021559155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72801912450952965390824413 27300717169107362021559155)
          ·
            refine ⟨40951075753661043032338733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27300717169107362021559155 40951075753661043032338733)
            ·
              refine ⟨15356653407622891137127025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40951075753661043032338733 15356653407622891137127025)
              ·
                refine ⟨11517490055717168352845269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15356653407622891137127025 11517490055717168352845269)
                ·
                  refine ⟨269941173180871133269811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11517490055717168352845269 269941173180871133269811)
                  ·
                    rfl

theorem cell23_4731377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 7].length) (baseStart_4731377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731377 prefixEnd_4731377 := by exact prefixLift 4731377
  have htrace : WordTrace (prefixWord ++ tailWord_4731377) baseStart_4731377 baseEnd_4731377 := by
    simpa [prefixWord, tailWord_4731377, baseEnd_4731377] using wordTrace_append hprefix tailTrace_4731377
  have hstable : (prefixWord ++ tailWord_4731377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731377).length < 2 ^ (prefixWord ++ tailWord_4731377).sum := by decide
  have hdescent : baseEnd_4731377 < baseStart_4731377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731387 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 3]
def baseStart_4731387 : Nat := 118140960795 + 4731387 * 2 ^ 59
def prefixEnd_4731387 : Nat := 4983230072969 + 3 ^ 40 * 4731387 * 2
def baseEnd_4731387 : Nat := 2429475693434385160303253

theorem tailTrace_4731387 : CollatzResearch.WordTrace tailWord_4731387 prefixEnd_4731387 2429475693434385160303253 := by
  unfold tailWord_4731387
  simp only [CollatzResearch.WordTrace]
  refine ⟨172567860910000430412040415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115045240606666953608026943 172567860910000430412040415)
  ·
    refine ⟨258851791365000645618060623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172567860910000430412040415 258851791365000645618060623)
    ·
      refine ⟨388277687047500968427090935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258851791365000645618060623 388277687047500968427090935)
      ·
        refine ⟨582416530571251452640636403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388277687047500968427090935 582416530571251452640636403)
        ·
          refine ⟨873624795856877178960954605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582416530571251452640636403 873624795856877178960954605)
          ·
            refine ⟨327609298446328942110357977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 873624795856877178960954605 327609298446328942110357977)
            ·
              refine ⟨245706973834746706582768483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327609298446328942110357977 245706973834746706582768483)
              ·
                refine ⟨368560460752120059874152725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245706973834746706582768483 368560460752120059874152725)
                ·
                  refine ⟨17276271597755627806600909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 368560460752120059874152725 17276271597755627806600909)
                  ·
                    refine ⟨6478601849158360427475341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17276271597755627806600909 6478601849158360427475341)
                    ·
                      refine ⟨2429475693434385160303253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6478601849158360427475341 2429475693434385160303253)
                      ·
                        rfl

theorem cell23_4731387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 3].length) (baseStart_4731387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731387 prefixEnd_4731387 := by exact prefixLift 4731387
  have htrace : WordTrace (prefixWord ++ tailWord_4731387) baseStart_4731387 baseEnd_4731387 := by
    simpa [prefixWord, tailWord_4731387, baseEnd_4731387] using wordTrace_append hprefix tailTrace_4731387
  have hstable : (prefixWord ++ tailWord_4731387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731387).length < 2 ^ (prefixWord ++ tailWord_4731387).sum := by decide
  have hdescent : baseEnd_4731387 < baseStart_4731387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731398 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_4731398 : Nat := 118140960795 + 4731398 * 2 ^ 59
def prefixEnd_4731398 : Nat := 4983230072969 + 3 ^ 40 * 4731398 * 2
def baseEnd_4731398 : Nat := 809827113907194872421901

theorem tailTrace_4731398 : CollatzResearch.WordTrace tailWord_4731398 prefixEnd_4731398 809827113907194872421901 := by
  unfold tailWord_4731398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5392758191030018102834089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 115045508075307052860460565 5392758191030018102834089)
  ·
    refine ⟨4044568643272513577125567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5392758191030018102834089 4044568643272513577125567)
    ·
      refine ⟨6066852964908770365688351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4044568643272513577125567 6066852964908770365688351)
      ·
        refine ⟨9100279447363155548532527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6066852964908770365688351 9100279447363155548532527)
        ·
          refine ⟨13650419171044733322798791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9100279447363155548532527 13650419171044733322798791)
          ·
            refine ⟨20475628756567099984198187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13650419171044733322798791 20475628756567099984198187)
            ·
              refine ⟨30713443134850649976297281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20475628756567099984198187 30713443134850649976297281)
              ·
                refine ⟨23035082351137987482222961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30713443134850649976297281 23035082351137987482222961)
                ·
                  refine ⟨17276311763353490611667221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23035082351137987482222961 17276311763353490611667221)
                  ·
                    refine ⟨809827113907194872421901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17276311763353490611667221 809827113907194872421901)
                    ·
                      rfl

theorem cell23_4731398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_4731398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731398 prefixEnd_4731398 := by exact prefixLift 4731398
  have htrace : WordTrace (prefixWord ++ tailWord_4731398) baseStart_4731398 baseEnd_4731398 := by
    simpa [prefixWord, tailWord_4731398, baseEnd_4731398] using wordTrace_append hprefix tailTrace_4731398
  have hstable : (prefixWord ++ tailWord_4731398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731398).length < 2 ^ (prefixWord ++ tailWord_4731398).sum := by decide
  have hdescent : baseEnd_4731398 < baseStart_4731398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731404 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 2, 3, 3]
def baseStart_4731404 : Nat := 118140960795 + 4731404 * 2 ^ 59
def prefixEnd_4731404 : Nat := 4983230072969 + 3 ^ 40 * 4731404 * 2
def baseEnd_4731404 : Nat := 2429484422605511593790675

theorem tailTrace_4731404 : CollatzResearch.WordTrace tailWord_4731404 prefixEnd_4731404 2429484422605511593790675 := by
  unfold tailWord_4731404
  simp only [CollatzResearch.WordTrace]
  refine ⟨86284240475469421157704633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115045653967292561543606177 86284240475469421157704633)
  ·
    refine ⟨64713180356602065868278475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86284240475469421157704633 64713180356602065868278475)
    ·
      refine ⟨97069770534903098802417713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64713180356602065868278475 97069770534903098802417713)
      ·
        refine ⟨72802327901177324101813285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97069770534903098802417713 72802327901177324101813285)
        ·
          refine ⟨13650436481470748269089991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72802327901177324101813285 13650436481470748269089991)
          ·
            refine ⟨20475654722206122403634987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13650436481470748269089991 20475654722206122403634987)
            ·
              refine ⟨30713482083309183605452481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20475654722206122403634987 30713482083309183605452481)
              ·
                refine ⟨23035111562481887704089361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30713482083309183605452481 23035111562481887704089361)
                ·
                  refine ⟨17276333671861415778067021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23035111562481887704089361 17276333671861415778067021)
                  ·
                    refine ⟨6478625126948030916775133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17276333671861415778067021 6478625126948030916775133)
                    ·
                      refine ⟨2429484422605511593790675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6478625126948030916775133 2429484422605511593790675)
                      ·
                        rfl

theorem cell23_4731404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_4731404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731404 prefixEnd_4731404 := by exact prefixLift 4731404
  have htrace : WordTrace (prefixWord ++ tailWord_4731404) baseStart_4731404 baseEnd_4731404 := by
    simpa [prefixWord, tailWord_4731404, baseEnd_4731404] using wordTrace_append hprefix tailTrace_4731404
  have hstable : (prefixWord ++ tailWord_4731404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731404).length < 2 ^ (prefixWord ++ tailWord_4731404).sum := by decide
  have hdescent : baseEnd_4731404 < baseStart_4731404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731467 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 8]
def baseStart_4731467 : Nat := 118140960795 + 4731467 * 2 ^ 59
def prefixEnd_4731467 : Nat := 4983230072969 + 3 ^ 40 * 4731467 * 2
def baseEnd_4731467 : Nat := 269946307987416094144765

theorem tailTrace_4731467 : CollatzResearch.WordTrace tailWord_4731467 prefixEnd_4731467 269946307987416094144765 := by
  unfold tailWord_4731467
  simp only [CollatzResearch.WordTrace]
  refine ⟨172570778749710604074952655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115047185833140402716635103 172570778749710604074952655)
  ·
    refine ⟨258856168124565906112428983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172570778749710604074952655 258856168124565906112428983)
    ·
      refine ⟨388284252186848859168643475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258856168124565906112428983 388284252186848859168643475)
      ·
        refine ⟨582426378280273288752965213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388284252186848859168643475 582426378280273288752965213)
        ·
          refine ⟨218409891855102483282361955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 582426378280273288752965213 218409891855102483282361955)
          ·
            refine ⟨327614837782653724923542933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218409891855102483282361955 327614837782653724923542933)
            ·
              refine ⟨15356945521061893355791075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 327614837782653724923542933 15356945521061893355791075)
              ·
                refine ⟨23035418281592840033686613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15356945521061893355791075 23035418281592840033686613)
                ·
                  refine ⟨269946307987416094144765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23035418281592840033686613 269946307987416094144765)
                  ·
                    rfl

theorem cell23_4731467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 8].length) (baseStart_4731467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731467 prefixEnd_4731467 := by exact prefixLift 4731467
  have htrace : WordTrace (prefixWord ++ tailWord_4731467) baseStart_4731467 baseEnd_4731467 := by
    simpa [prefixWord, tailWord_4731467, baseEnd_4731467] using wordTrace_append hprefix tailTrace_4731467
  have hstable : (prefixWord ++ tailWord_4731467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731467).length < 2 ^ (prefixWord ++ tailWord_4731467).sum := by decide
  have hdescent : baseEnd_4731467 < baseStart_4731467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731471 : List Nat := [1, 1, 2, 1, 1, 2, 4, 6, 1, 4]
def baseStart_4731471 : Nat := 118140960795 + 4731471 * 2 ^ 59
def prefixEnd_4731471 : Nat := 4983230072969 + 3 ^ 40 * 4731471 * 2
def baseEnd_4731471 : Nat := 809839608603120943884289

theorem tailTrace_4731471 : CollatzResearch.WordTrace tailWord_4731471 prefixEnd_4731471 809839608603120943884289 := by
  unfold tailWord_4731471
  simp only [CollatzResearch.WordTrace]
  refine ⟨172570924641696112758098267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115047283094464075172065511 172570924641696112758098267)
  ·
    refine ⟨258856386962544169137147401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172570924641696112758098267 258856386962544169137147401)
    ·
      refine ⟨194142290221908126852860551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258856386962544169137147401 194142290221908126852860551)
      ·
        refine ⟨291213435332862190279290827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194142290221908126852860551 291213435332862190279290827)
        ·
          refine ⟨436820152999293285418936241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291213435332862190279290827 436820152999293285418936241)
          ·
            refine ⟨327615114749469964064202181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436820152999293285418936241 327615114749469964064202181)
            ·
              refine ⟨61427834015525618262037909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327615114749469964064202181 61427834015525618262037909)
              ·
                refine ⟨2879429719477763356033027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61427834015525618262037909 2879429719477763356033027)
                ·
                  refine ⟨4319144579216645034049541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2879429719477763356033027 4319144579216645034049541)
                  ·
                    refine ⟨809839608603120943884289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4319144579216645034049541 809839608603120943884289)
                    ·
                      rfl

theorem cell23_4731471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 4].length) (baseStart_4731471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731471 prefixEnd_4731471 := by exact prefixLift 4731471
  have htrace : WordTrace (prefixWord ++ tailWord_4731471) baseStart_4731471 baseEnd_4731471 := by
    simpa [prefixWord, tailWord_4731471, baseEnd_4731471] using wordTrace_append hprefix tailTrace_4731471
  have hstable : (prefixWord ++ tailWord_4731471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731471).length < 2 ^ (prefixWord ++ tailWord_4731471).sum := by decide
  have hdescent : baseEnd_4731471 < baseStart_4731471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731487 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_4731487 : Nat := 118140960795 + 4731487 * 2 ^ 59
def prefixEnd_4731487 : Nat := 4983230072969 + 3 ^ 40 * 4731487 * 2
def baseEnd_4731487 : Nat := 2429527041499834769052793

theorem tailTrace_4731487 : CollatzResearch.WordTrace tailWord_4731487 prefixEnd_4731487 2429527041499834769052793 := by
  unfold tailWord_4731487
  simp only [CollatzResearch.WordTrace]
  refine ⟨172571508209638147490680715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115047672139758764993787143 172571508209638147490680715)
  ·
    refine ⟨258857262314457221236021073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172571508209638147490680715 258857262314457221236021073)
    ·
      refine ⟨194142946735842915927015805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258857262314457221236021073 194142946735842915927015805)
      ·
        refine ⟨72803605025941093472630927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194142946735842915927015805 72803605025941093472630927)
        ·
          refine ⟨109205407538911640208946391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72803605025941093472630927 109205407538911640208946391)
          ·
            refine ⟨163808111308367460313419587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109205407538911640208946391 163808111308367460313419587)
            ·
              refine ⟨245712166962551190470129381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163808111308367460313419587 245712166962551190470129381)
              ·
                refine ⟨46071031305478348213149259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245712166962551190470129381 46071031305478348213149259)
                ·
                  refine ⟨69106546958217522319723889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46071031305478348213149259 69106546958217522319723889)
                  ·
                    refine ⟨51829910218663141739792917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69106546958217522319723889 51829910218663141739792917)
                    ·
                      refine ⟨2429527041499834769052793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51829910218663141739792917 2429527041499834769052793)
                      ·
                        rfl

theorem cell23_4731487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_4731487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731487 prefixEnd_4731487 := by exact prefixLift 4731487
  have htrace : WordTrace (prefixWord ++ tailWord_4731487) baseStart_4731487 baseEnd_4731487 := by
    simpa [prefixWord, tailWord_4731487, baseEnd_4731487] using wordTrace_append hprefix tailTrace_4731487
  have hstable : (prefixWord ++ tailWord_4731487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731487).length < 2 ^ (prefixWord ++ tailWord_4731487).sum := by decide
  have hdescent : baseEnd_4731487 < baseStart_4731487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731507 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 5]
def baseStart_4731507 : Nat := 118140960795 + 4731507 * 2 ^ 59
def prefixEnd_4731507 : Nat := 4983230072969 + 3 ^ 40 * 4731507 * 2
def baseEnd_4731507 : Nat := 2429537311112924690802701

theorem tailTrace_4731507 : CollatzResearch.WordTrace tailWord_4731507 prefixEnd_4731507 2429537311112924690802701 := by
  unfold tailWord_4731507
  simp only [CollatzResearch.WordTrace]
  refine ⟨172572237669565690906408775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115048158446377127270939183 172572237669565690906408775)
  ·
    refine ⟨258858356504348536359613163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172572237669565690906408775 258858356504348536359613163)
    ·
      refine ⟨388287534756522804539419745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258858356504348536359613163 388287534756522804539419745)
      ·
        refine ⟨291215651067392103404564809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388287534756522804539419745 291215651067392103404564809)
        ·
          refine ⟨218411738300544077553423607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291215651067392103404564809 218411738300544077553423607)
          ·
            refine ⟨327617607450816116330135411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218411738300544077553423607 327617607450816116330135411)
            ·
              refine ⟨491426411176224174495203117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327617607450816116330135411 491426411176224174495203117)
              ·
                refine ⟨184284904191084065435701169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491426411176224174495203117 184284904191084065435701169)
                ·
                  refine ⟨138213678143313049076775877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184284904191084065435701169 138213678143313049076775877)
                  ·
                    refine ⟨25915064651871196701895477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138213678143313049076775877 25915064651871196701895477)
                    ·
                      refine ⟨2429537311112924690802701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25915064651871196701895477 2429537311112924690802701)
                      ·
                        rfl

theorem cell23_4731507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_4731507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731507 prefixEnd_4731507 := by exact prefixLift 4731507
  have htrace : WordTrace (prefixWord ++ tailWord_4731507) baseStart_4731507 baseEnd_4731507 := by
    simpa [prefixWord, tailWord_4731507, baseEnd_4731507] using wordTrace_append hprefix tailTrace_4731507
  have hstable : (prefixWord ++ tailWord_4731507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731507).length < 2 ^ (prefixWord ++ tailWord_4731507).sum := by decide
  have hdescent : baseEnd_4731507 < baseStart_4731507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731565 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_4731565 : Nat := 118140960795 + 4731565 * 2 ^ 59
def prefixEnd_4731565 : Nat := 4983230072969 + 3 ^ 40 * 4731565 * 2
def baseEnd_4731565 : Nat := 809855697663628487959145

theorem tailTrace_4731565 : CollatzResearch.WordTrace tailWord_4731565 prefixEnd_4731565 809855697663628487959145 := by
  unfold tailWord_4731565
  simp only [CollatzResearch.WordTrace]
  refine ⟨172574353103355566812020149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115049568735570377874680099 172574353103355566812020149)
  ·
    refine ⟨16178845603439584388626889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172574353103355566812020149 16178845603439584388626889)
    ·
      refine ⟨12134134202579688291470167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16178845603439584388626889 12134134202579688291470167)
      ·
        refine ⟨18201201303869532437205251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12134134202579688291470167 18201201303869532437205251)
        ·
          refine ⟨27301801955804298655807877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18201201303869532437205251 27301801955804298655807877)
          ·
            refine ⟨5119087866713305997963977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27301801955804298655807877 5119087866713305997963977)
            ·
              refine ⟨3839315900034979498472983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5119087866713305997963977 3839315900034979498472983)
              ·
                refine ⟨5758973850052469247709475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3839315900034979498472983 5758973850052469247709475)
                ·
                  refine ⟨8638460775078703871564213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5758973850052469247709475 8638460775078703871564213)
                  ·
                    refine ⟨809855697663628487959145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8638460775078703871564213 809855697663628487959145)
                    ·
                      rfl

theorem cell23_4731565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_4731565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731565 prefixEnd_4731565 := by exact prefixLift 4731565
  have htrace : WordTrace (prefixWord ++ tailWord_4731565) baseStart_4731565 baseEnd_4731565 := by
    simpa [prefixWord, tailWord_4731565, baseEnd_4731565] using wordTrace_append hprefix tailTrace_4731565
  have hstable : (prefixWord ++ tailWord_4731565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731565).length < 2 ^ (prefixWord ++ tailWord_4731565).sum := by decide
  have hdescent : baseEnd_4731565 < baseStart_4731565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731598 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_4731598 : Nat := 118140960795 + 4731598 * 2 ^ 59
def prefixEnd_4731598 : Nat := 4983230072969 + 3 ^ 40 * 4731598 * 2
def baseEnd_4731598 : Nat := 2429584037852483834764783

theorem tailTrace_4731598 : CollatzResearch.WordTrace tailWord_4731598 prefixEnd_4731598 2429584037852483834764783 := by
  unfold tailWord_4731598
  simp only [CollatzResearch.WordTrace]
  refine ⟨21571944589029501680996431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 115050371141490675631980965 21571944589029501680996431)
  ·
    refine ⟨32357916883544252521494647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21571944589029501680996431 32357916883544252521494647)
    ·
      refine ⟨48536875325316378782241971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32357916883544252521494647 48536875325316378782241971)
      ·
        refine ⟨72805312987974568173362957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48536875325316378782241971 72805312987974568173362957)
        ·
          refine ⟨27301992370490463065011109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72805312987974568173362957 27301992370490463065011109)
          ·
            refine ⟨5119123569466961824689583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27301992370490463065011109 5119123569466961824689583)
            ·
              refine ⟨7678685354200442737034375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119123569466961824689583 7678685354200442737034375)
              ·
                refine ⟨11518028031300664105551563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7678685354200442737034375 11518028031300664105551563)
                ·
                  refine ⟨17277042046950996158327345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11518028031300664105551563 17277042046950996158327345)
                  ·
                    refine ⟨12957781535213247118745509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17277042046950996158327345 12957781535213247118745509)
                    ·
                      refine ⟨2429584037852483834764783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12957781535213247118745509 2429584037852483834764783)
                      ·
                        rfl

theorem cell23_4731598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_4731598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731598 prefixEnd_4731598 := by exact prefixLift 4731598
  have htrace : WordTrace (prefixWord ++ tailWord_4731598) baseStart_4731598 baseEnd_4731598 := by
    simpa [prefixWord, tailWord_4731598, baseEnd_4731598] using wordTrace_append hprefix tailTrace_4731598
  have hstable : (prefixWord ++ tailWord_4731598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731598).length < 2 ^ (prefixWord ++ tailWord_4731598).sum := by decide
  have hdescent : baseEnd_4731598 < baseStart_4731598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731619 : List Nat := [1, 1, 1, 7, 1, 3, 1, 3, 1, 2, 2]
def baseStart_4731619 : Nat := 118140960795 + 4731619 * 2 ^ 59
def prefixEnd_4731619 : Nat := 4983230072969 + 3 ^ 40 * 4731619 * 2
def baseEnd_4731619 : Nat := 2429594820946228252602187

theorem tailTrace_4731619 : CollatzResearch.WordTrace tailWord_4731619 prefixEnd_4731619 2429594820946228252602187 := by
  unfold tailWord_4731619
  simp only [CollatzResearch.WordTrace]
  refine ⟨172576322645159934034485911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115050881763439956022990607 172576322645159934034485911)
  ·
    refine ⟨258864483967739901051728867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172576322645159934034485911 258864483967739901051728867)
    ·
      refine ⟨388296725951609851577593301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258864483967739901051728867 388296725951609851577593301)
      ·
        refine ⟨9100704514490855896349843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 388296725951609851577593301 9100704514490855896349843)
        ·
          refine ⟨13651056771736283844524765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9100704514490855896349843 13651056771736283844524765)
          ·
            refine ⟨5119146289401106441696787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13651056771736283844524765 5119146289401106441696787)
            ·
              refine ⟨7678719434101659662545181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119146289401106441696787 7678719434101659662545181)
              ·
                refine ⟨2879519787788122373454443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7678719434101659662545181 2879519787788122373454443)
                ·
                  refine ⟨4319279681682183560181665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2879519787788122373454443 4319279681682183560181665)
                  ·
                    refine ⟨3239459761261637670136249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4319279681682183560181665 3239459761261637670136249)
                    ·
                      refine ⟨2429594820946228252602187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239459761261637670136249 2429594820946228252602187)
                      ·
                        rfl

theorem cell23_4731619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_4731619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731619 prefixEnd_4731619 := by exact prefixLift 4731619
  have htrace : WordTrace (prefixWord ++ tailWord_4731619) baseStart_4731619 baseEnd_4731619 := by
    simpa [prefixWord, tailWord_4731619, baseEnd_4731619] using wordTrace_append hprefix tailTrace_4731619
  have hstable : (prefixWord ++ tailWord_4731619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731619).length < 2 ^ (prefixWord ++ tailWord_4731619).sum := by decide
  have hdescent : baseEnd_4731619 < baseStart_4731619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731636 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4731636 : Nat := 118140960795 + 4731636 * 2 ^ 59
def prefixEnd_4731636 : Nat := 4983230072969 + 3 ^ 40 * 4731636 * 2
def baseEnd_4731636 : Nat := 2429603550117354686089609

theorem tailTrace_4731636 : CollatzResearch.WordTrace tailWord_4731636 prefixEnd_4731636 2429603550117354686089609 := by
  unfold tailWord_4731636
  simp only [CollatzResearch.WordTrace]
  refine ⟨86288471343049172968927381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 115051295124065563958569841 86288471343049172968927381)
  ·
    refine ⟨4044772094205429982918471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86288471343049172968927381 4044772094205429982918471)
    ·
      refine ⟨6067158141308144974377707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4044772094205429982918471 6067158141308144974377707)
      ·
        refine ⟨9100737211962217461566561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6067158141308144974377707 9100737211962217461566561)
        ·
          refine ⟨6825552908971663096174921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9100737211962217461566561 6825552908971663096174921)
          ·
            refine ⟨5119164681728747322131191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6825552908971663096174921 5119164681728747322131191)
            ·
              refine ⟨7678747022593120983196787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119164681728747322131191 7678747022593120983196787)
              ·
                refine ⟨11518120533889681474795181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7678747022593120983196787 11518120533889681474795181)
                ·
                  refine ⟨4319295200208630553048193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11518120533889681474795181 4319295200208630553048193)
                  ·
                    refine ⟨3239471400156472914786145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4319295200208630553048193 3239471400156472914786145)
                    ·
                      refine ⟨2429603550117354686089609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239471400156472914786145 2429603550117354686089609)
                      ·
                        rfl

theorem cell23_4731636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4731636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731636 prefixEnd_4731636 := by exact prefixLift 4731636
  have htrace : WordTrace (prefixWord ++ tailWord_4731636) baseStart_4731636 baseEnd_4731636 := by
    simpa [prefixWord, tailWord_4731636, baseEnd_4731636] using wordTrace_append hprefix tailTrace_4731636
  have hstable : (prefixWord ++ tailWord_4731636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731636).length < 2 ^ (prefixWord ++ tailWord_4731636).sum := by decide
  have hdescent : baseEnd_4731636 < baseStart_4731636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731658 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_4731658 : Nat := 118140960795 + 4731658 * 2 ^ 59
def prefixEnd_4731658 : Nat := 4983230072969 + 3 ^ 40 * 4731658 * 2
def baseEnd_4731658 : Nat := 2429614846691753600014507

theorem tailTrace_4731658 : CollatzResearch.WordTrace tailWord_4731658 prefixEnd_4731658 2429614846691753600014507 := by
  unfold tailWord_4731658
  simp only [CollatzResearch.WordTrace]
  refine ⟨43144436273004660923788907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115051830061345762463437085 43144436273004660923788907)
  ·
    refine ⟨64716654409506991385683361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43144436273004660923788907 64716654409506991385683361)
    ·
      refine ⟨48537490807130243539262521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64716654409506991385683361 48537490807130243539262521)
      ·
        refine ⟨36403118105347682654446891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48537490807130243539262521 36403118105347682654446891)
        ·
          refine ⟨54604677158021523981670337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36403118105347682654446891 54604677158021523981670337)
          ·
            refine ⟨40953507868516142986252753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54604677158021523981670337 40953507868516142986252753)
            ·
              refine ⟨30715130901387107239689565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40953507868516142986252753 30715130901387107239689565)
              ·
                refine ⟨11518174088020165214883587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30715130901387107239689565 11518174088020165214883587)
                ·
                  refine ⟨17277261132030247822325381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11518174088020165214883587 17277261132030247822325381)
                  ·
                    refine ⟨3239486462255671466686009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17277261132030247822325381 3239486462255671466686009)
                    ·
                      refine ⟨2429614846691753600014507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239486462255671466686009 2429614846691753600014507)
                      ·
                        rfl

theorem cell23_4731658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_4731658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731658 prefixEnd_4731658 := by exact prefixLift 4731658
  have htrace : WordTrace (prefixWord ++ tailWord_4731658) baseStart_4731658 baseEnd_4731658 := by
    simpa [prefixWord, tailWord_4731658, baseEnd_4731658] using wordTrace_append hprefix tailTrace_4731658
  have hstable : (prefixWord ++ tailWord_4731658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731658).length < 2 ^ (prefixWord ++ tailWord_4731658).sum := by decide
  have hdescent : baseEnd_4731658 < baseStart_4731658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731698 : List Nat := [3, 2, 1, 1, 3, 1, 3, 4, 5]
def baseStart_4731698 : Nat := 118140960795 + 4731698 * 2 ^ 59
def prefixEnd_4731698 : Nat := 4983230072969 + 3 ^ 40 * 4731698 * 2
def baseEnd_4731698 : Nat := 269959487324214827057147

theorem tailTrace_4731698 : CollatzResearch.WordTrace tailWord_4731698 prefixEnd_4731698 269959487324214827057147 := by
  unfold tailWord_4731698
  simp only [CollatzResearch.WordTrace]
  refine ⟨43144801002968432631652937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115052802674582487017741165 43144801002968432631652937)
  ·
    refine ⟨32358600752226324473739703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43144801002968432631652937 32358600752226324473739703)
    ·
      refine ⟨48537901128339486710609555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32358600752226324473739703 48537901128339486710609555)
      ·
        refine ⟨72806851692509230065914333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48537901128339486710609555 72806851692509230065914333)
        ·
          refine ⟨27302569384690961274717875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72806851692509230065914333 27302569384690961274717875)
          ·
            refine ⟨40953854077036441912076813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27302569384690961274717875 40953854077036441912076813)
            ·
              refine ⟨15357695278888665717028805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40953854077036441912076813 15357695278888665717028805)
              ·
                refine ⟨2879567864791624821942901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15357695278888665717028805 2879567864791624821942901)
                ·
                  refine ⟨269959487324214827057147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2879567864791624821942901 269959487324214827057147)
                  ·
                    rfl

theorem cell23_4731698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_4731698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731698 prefixEnd_4731698 := by exact prefixLift 4731698
  have htrace : WordTrace (prefixWord ++ tailWord_4731698) baseStart_4731698 baseEnd_4731698 := by
    simpa [prefixWord, tailWord_4731698, baseEnd_4731698] using wordTrace_append hprefix tailTrace_4731698
  have hstable : (prefixWord ++ tailWord_4731698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731698).length < 2 ^ (prefixWord ++ tailWord_4731698).sum := by decide
  have hdescent : baseEnd_4731698 < baseStart_4731698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731765 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_4731765 : Nat := 118140960795 + 4731765 * 2 ^ 59
def prefixEnd_4731765 : Nat := 4983230072969 + 3 ^ 40 * 4731765 * 2
def baseEnd_4731765 : Nat := 2429669789121784681376515

theorem tailTrace_4731765 : CollatzResearch.WordTrace tailWord_4731765 prefixEnd_4731765 2429669789121784681376515 := by
  unfold tailWord_4731765
  simp only [CollatzResearch.WordTrace]
  refine ⟨172581647702631000969300749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115054431801754000646200499 172581647702631000969300749)
  ·
    refine ⟨64718117888486625363487781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172581647702631000969300749 64718117888486625363487781)
    ·
      refine ⟨12134647104091242255653959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64718117888486625363487781 12134647104091242255653959)
      ·
        refine ⟨18201970656136863383480939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12134647104091242255653959 18201970656136863383480939)
        ·
          refine ⟨27302955984205295075221409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18201970656136863383480939 27302955984205295075221409)
          ·
            refine ⟨20477216988153971306416057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27302955984205295075221409 20477216988153971306416057)
            ·
              refine ⟨15357912741115478479812043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20477216988153971306416057 15357912741115478479812043)
              ·
                refine ⟨23036869111673217719718065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15357912741115478479812043 23036869111673217719718065)
                ·
                  refine ⟨17277651833754913289788549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23036869111673217719718065 17277651833754913289788549)
                  ·
                    refine ⟨3239559718829046241835353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17277651833754913289788549 3239559718829046241835353)
                    ·
                      refine ⟨2429669789121784681376515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3239559718829046241835353 2429669789121784681376515)
                      ·
                        rfl

theorem cell23_4731765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_4731765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731765 prefixEnd_4731765 := by exact prefixLift 4731765
  have htrace : WordTrace (prefixWord ++ tailWord_4731765) baseStart_4731765 baseEnd_4731765 := by
    simpa [prefixWord, tailWord_4731765, baseEnd_4731765] using wordTrace_append hprefix tailTrace_4731765
  have hstable : (prefixWord ++ tailWord_4731765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731765).length < 2 ^ (prefixWord ++ tailWord_4731765).sum := by decide
  have hdescent : baseEnd_4731765 < baseStart_4731765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731771 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 6]
def baseStart_4731771 : Nat := 118140960795 + 4731771 * 2 ^ 59
def prefixEnd_4731771 : Nat := 4983230072969 + 3 ^ 40 * 4731771 * 2
def baseEnd_4731771 : Nat := 269963652222856850877943

theorem tailTrace_4731771 : CollatzResearch.WordTrace tailWord_4731771 prefixEnd_4731771 269963652222856850877943 := by
  unfold tailWord_4731771
  simp only [CollatzResearch.WordTrace]
  refine ⟨172581866540609263994019167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115054577693739509329346111 172581866540609263994019167)
  ·
    refine ⟨258872799810913895991028751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172581866540609263994019167 258872799810913895991028751)
    ·
      refine ⟨388309199716370843986543127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258872799810913895991028751 388309199716370843986543127)
      ·
        refine ⟨582463799574556265979814691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388309199716370843986543127 582463799574556265979814691)
        ·
          refine ⟨873695699361834398969722037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582463799574556265979814691 873695699361834398969722037)
          ·
            refine ⟨81908971815171974903411441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 873695699361834398969722037 81908971815171974903411441)
            ·
              refine ⟨61431728861378981177558581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81908971815171974903411441 61431728861378981177558581)
              ·
                refine ⟨5759224580754279485396117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61431728861378981177558581 5759224580754279485396117)
                ·
                  refine ⟨269963652222856850877943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5759224580754279485396117 269963652222856850877943)
                  ·
                    rfl

theorem cell23_4731771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 6].length) (baseStart_4731771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731771 prefixEnd_4731771 := by exact prefixLift 4731771
  have htrace : WordTrace (prefixWord ++ tailWord_4731771) baseStart_4731771 baseEnd_4731771 := by
    simpa [prefixWord, tailWord_4731771, baseEnd_4731771] using wordTrace_append hprefix tailTrace_4731771
  have hstable : (prefixWord ++ tailWord_4731771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731771).length < 2 ^ (prefixWord ++ tailWord_4731771).sum := by decide
  have hdescent : baseEnd_4731771 < baseStart_4731771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731801 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 5, 5]
def baseStart_4731801 : Nat := 118140960795 + 4731801 * 2 ^ 59
def prefixEnd_4731801 : Nat := 4983230072969 + 3 ^ 40 * 4731801 * 2
def baseEnd_4731801 : Nat := 809896091475115513508783

theorem tailTrace_4731801 : CollatzResearch.WordTrace tailWord_4731801 prefixEnd_4731801 809896091475115513508783 := by
  unfold tailWord_4731801
  simp only [CollatzResearch.WordTrace]
  refine ⟨172582960730500579117611257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115055307153667052745074171 172582960730500579117611257)
  ·
    refine ⟨129437220547875434338208443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172582960730500579117611257 129437220547875434338208443)
    ·
      refine ⟨194155830821813151507312665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129437220547875434338208443 194155830821813151507312665)
      ·
        refine ⟨145616873116359863630484499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194155830821813151507312665 145616873116359863630484499)
        ·
          refine ⟨218425309674539795445726749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145616873116359863630484499 218425309674539795445726749)
          ·
            refine ⟨81909491127952423292147531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218425309674539795445726749 81909491127952423292147531)
            ·
              refine ⟨122864236691928634938221297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81909491127952423292147531 122864236691928634938221297)
              ·
                refine ⟨92148177518946476203665973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122864236691928634938221297 92148177518946476203665973)
                ·
                  refine ⟨8638891642401232144093685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92148177518946476203665973 8638891642401232144093685)
                  ·
                    refine ⟨809896091475115513508783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8638891642401232144093685 809896091475115513508783)
                    ·
                      rfl

theorem cell23_4731801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_4731801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731801 prefixEnd_4731801 := by exact prefixLift 4731801
  have htrace : WordTrace (prefixWord ++ tailWord_4731801) baseStart_4731801 baseEnd_4731801 := by
    simpa [prefixWord, tailWord_4731801, baseEnd_4731801] using wordTrace_append hprefix tailTrace_4731801
  have hstable : (prefixWord ++ tailWord_4731801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731801).length < 2 ^ (prefixWord ++ tailWord_4731801).sum := by decide
  have hdescent : baseEnd_4731801 < baseStart_4731801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731809 : List Nat := [1, 2, 3, 4, 1, 2, 3, 2, 1, 4]
def baseStart_4731809 : Nat := 118140960795 + 4731809 * 2 ^ 59
def prefixEnd_4731809 : Nat := 4983230072969 + 3 ^ 40 * 4731809 * 2
def baseEnd_4731809 : Nat := 809897460756860836408771

theorem tailTrace_4731809 : CollatzResearch.WordTrace tailWord_4731809 prefixEnd_4731809 809897460756860836408771 := by
  unfold tailWord_4731809
  simp only [CollatzResearch.WordTrace]
  refine ⟨172583252514471596483902481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115055501676314397655934987 172583252514471596483902481)
  ·
    refine ⟨129437439385853697362926861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172583252514471596483902481 129437439385853697362926861)
    ·
      refine ⟨48539039769695136511097573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129437439385853697362926861 48539039769695136511097573)
      ·
        refine ⟨9101069956817838095830795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48539039769695136511097573 9101069956817838095830795)
        ·
          refine ⟨13651604935226757143746193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9101069956817838095830795 13651604935226757143746193)
          ·
            refine ⟨10238703701420067857809645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13651604935226757143746193 10238703701420067857809645)
            ·
              refine ⟨3839513888032525446678617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10238703701420067857809645 3839513888032525446678617)
              ·
                refine ⟨2879635416024394085008963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3839513888032525446678617 2879635416024394085008963)
                ·
                  refine ⟨4319453124036591127513445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2879635416024394085008963 4319453124036591127513445)
                  ·
                    refine ⟨809897460756860836408771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4319453124036591127513445 809897460756860836408771)
                    ·
                      rfl

theorem cell23_4731809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_4731809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731809 prefixEnd_4731809 := by exact prefixLift 4731809
  have htrace : WordTrace (prefixWord ++ tailWord_4731809) baseStart_4731809 baseEnd_4731809 := by
    simpa [prefixWord, tailWord_4731809, baseEnd_4731809] using wordTrace_append hprefix tailTrace_4731809
  have hstable : (prefixWord ++ tailWord_4731809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731809).length < 2 ^ (prefixWord ++ tailWord_4731809).sum := by decide
  have hdescent : baseEnd_4731809 < baseStart_4731809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731861 : List Nat := [1, 3, 2, 3, 14]
def baseStart_4731861 : Nat := 118140960795 + 4731861 * 2 ^ 59
def prefixEnd_4731861 : Nat := 4983230072969 + 3 ^ 40 * 4731861 * 2
def baseEnd_4731861 : Nat := 3332947988017306317937

theorem tailTrace_4731861 : CollatzResearch.WordTrace tailWord_4731861 prefixEnd_4731861 3332947988017306317937 := by
  unfold tailWord_4731861
  simp only [CollatzResearch.WordTrace]
  refine ⟨172585149110283209364795437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115056766073522139576530291 172585149110283209364795437)
  ·
    refine ⟨64719430916356203511798289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172585149110283209364795437 64719430916356203511798289)
    ·
      refine ⟨48539573187267152633848717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64719430916356203511798289 48539573187267152633848717)
      ·
        refine ⟨18202339945225182237693269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48539573187267152633848717 18202339945225182237693269)
        ·
          refine ⟨3332947988017306317937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 18202339945225182237693269 3332947988017306317937)
          ·
            rfl

theorem cell23_4731861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 14].length) (baseStart_4731861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731861 prefixEnd_4731861 := by exact prefixLift 4731861
  have htrace : WordTrace (prefixWord ++ tailWord_4731861) baseStart_4731861 baseEnd_4731861 := by
    simpa [prefixWord, tailWord_4731861, baseEnd_4731861] using wordTrace_append hprefix tailTrace_4731861
  have hstable : (prefixWord ++ tailWord_4731861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731861).length < 2 ^ (prefixWord ++ tailWord_4731861).sum := by decide
  have hdescent : baseEnd_4731861 < baseStart_4731861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731865 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 2, 4]
def baseStart_4731865 : Nat := 118140960795 + 4731865 * 2 ^ 59
def prefixEnd_4731865 : Nat := 4983230072969 + 3 ^ 40 * 4731865 * 2
def baseEnd_4731865 : Nat := 809907045729078096708685

theorem tailTrace_4731865 : CollatzResearch.WordTrace tailWord_4731865 prefixEnd_4731865 809907045729078096708685 := by
  unfold tailWord_4731865
  simp only [CollatzResearch.WordTrace]
  refine ⟨172585295002268718047941049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 115056863334845812031960699 172585295002268718047941049)
  ·
    refine ⟨129438971251701538535955787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172585295002268718047941049 129438971251701538535955787)
    ·
      refine ⟨194158456877552307803933681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129438971251701538535955787 194158456877552307803933681)
      ·
        refine ⟨145618842658164230852950261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194158456877552307803933681 145618842658164230852950261)
        ·
          refine ⟨13651766499202896642464087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145618842658164230852950261 13651766499202896642464087)
          ·
            refine ⟨20477649748804344963696131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13651766499202896642464087 20477649748804344963696131)
            ·
              refine ⟨30716474623206517445544197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20477649748804344963696131 30716474623206517445544197)
              ·
                refine ⟨5759338991851222021039537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30716474623206517445544197 5759338991851222021039537)
                ·
                  refine ⟨4319504243888416515779653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5759338991851222021039537 4319504243888416515779653)
                  ·
                    refine ⟨809907045729078096708685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4319504243888416515779653 809907045729078096708685)
                    ·
                      rfl

theorem cell23_4731865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 4].length) (baseStart_4731865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731865 prefixEnd_4731865 := by exact prefixLift 4731865
  have htrace : WordTrace (prefixWord ++ tailWord_4731865) baseStart_4731865 baseEnd_4731865 := by
    simpa [prefixWord, tailWord_4731865, baseEnd_4731865] using wordTrace_append hprefix tailTrace_4731865
  have hstable : (prefixWord ++ tailWord_4731865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731865).length < 2 ^ (prefixWord ++ tailWord_4731865).sum := by decide
  have hdescent : baseEnd_4731865 < baseStart_4731865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4731866 : List Nat := [3, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3]
def baseStart_4731866 : Nat := 118140960795 + 4731866 * 2 ^ 59
def prefixEnd_4731866 : Nat := 4983230072969 + 3 ^ 40 * 4731866 * 2
def baseEnd_4731866 : Nat := 2429721650667888786213551

theorem tailTrace_4731866 : CollatzResearch.WordTrace tailWord_4731866 prefixEnd_4731866 2429721650667888786213551 := by
  unfold tailWord_4731866
  simp only [CollatzResearch.WordTrace]
  refine ⟨43146332868816273804681863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 115056887650176730145818301 43146332868816273804681863)
  ·
    refine ⟨64719499303224410707022795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43146332868816273804681863 64719499303224410707022795)
    ·
      refine ⟨97079248954836616060534193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64719499303224410707022795 97079248954836616060534193)
      ·
        refine ⟨72809436716127462045400645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97079248954836616060534193 72809436716127462045400645)
        ·
          refine ⟨13651769384273899133512621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72809436716127462045400645 13651769384273899133512621)
          ·
            refine ⟨5119413519102712175067233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13651769384273899133512621 5119413519102712175067233)
            ·
              refine ⟨3839560139327034131300425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5119413519102712175067233 3839560139327034131300425)
              ·
                refine ⟨2879670104495275598475319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3839560139327034131300425 2879670104495275598475319)
                ·
                  refine ⟨4319505156742913397712979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2879670104495275598475319 4319505156742913397712979)
                  ·
                    refine ⟨6479257735114370096569469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4319505156742913397712979 6479257735114370096569469)
                    ·
                      refine ⟨2429721650667888786213551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6479257735114370096569469 2429721650667888786213551)
                      ·
                        rfl

theorem cell23_4731866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_4731866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4731866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4731866 prefixEnd_4731866 := by exact prefixLift 4731866
  have htrace : WordTrace (prefixWord ++ tailWord_4731866) baseStart_4731866 baseEnd_4731866 := by
    simpa [prefixWord, tailWord_4731866, baseEnd_4731866] using wordTrace_append hprefix tailTrace_4731866
  have hstable : (prefixWord ++ tailWord_4731866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4731866).length < 2 ^ (prefixWord ++ tailWord_4731866).sum := by decide
  have hdescent : baseEnd_4731866 < baseStart_4731866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4731866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
