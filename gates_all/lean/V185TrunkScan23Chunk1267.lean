import V185TrunkScan23Chunk1266

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7506009 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 3]
def baseStart_7506009 : Nat := 118140960795 + 7506009 * 2 ^ 59
def prefixEnd_7506009 : Nat := 4983230072969 + 3 ^ 40 * 7506009 * 2
def baseEnd_7506009 : Nat := 3854190413973628438967999

theorem tailTrace_7506009 : CollatzResearch.WordTrace tailWord_7506009 prefixEnd_7506009 3854190413973628438967999 := by
  unfold tailWord_7506009
  simp only [CollatzResearch.WordTrace]
  refine ⟨273766639064018792123105081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182511092709345861415403387 273766639064018792123105081)
  ·
    refine ⟨205324979298014094092328811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273766639064018792123105081 205324979298014094092328811)
    ·
      refine ⟨307987468947021141138493217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205324979298014094092328811 307987468947021141138493217)
      ·
        refine ⟨230990601710265855853869913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307987468947021141138493217 230990601710265855853869913)
        ·
          refine ⟨173242951282699391890402435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230990601710265855853869913 173242951282699391890402435)
          ·
            refine ⟨259864426924049087835603653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173242951282699391890402435 259864426924049087835603653)
            ·
              refine ⟨48724580048259203969175685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259864426924049087835603653 48724580048259203969175685)
              ·
                refine ⟨9135858759048600744220441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48724580048259203969175685 9135858759048600744220441)
                ·
                  refine ⟨6851894069286450558165331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9135858759048600744220441 6851894069286450558165331)
                  ·
                    refine ⟨10277841103929675837247997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6851894069286450558165331 10277841103929675837247997)
                    ·
                      refine ⟨3854190413973628438967999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10277841103929675837247997 3854190413973628438967999)
                      ·
                        rfl

theorem cell23_7506009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_7506009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506009 prefixEnd_7506009 := by exact prefixLift 7506009
  have htrace : WordTrace (prefixWord ++ tailWord_7506009) baseStart_7506009 baseEnd_7506009 := by
    simpa [prefixWord, tailWord_7506009, baseEnd_7506009] using wordTrace_append hprefix tailTrace_7506009
  have hstable : (prefixWord ++ tailWord_7506009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506009).length < 2 ^ (prefixWord ++ tailWord_7506009).sum := by decide
  have hdescent : baseEnd_7506009 < baseStart_7506009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506025 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 1, 8]
def baseStart_7506025 : Nat := 118140960795 + 7506025 * 2 ^ 59
def prefixEnd_7506025 : Nat := 4983230072969 + 3 ^ 40 * 7506025 * 2
def baseEnd_7506025 : Nat := 1284732876554700125455975

theorem tailTrace_7506025 : CollatzResearch.WordTrace tailWord_7506025 prefixEnd_7506025 1284732876554700125455975 := by
  unfold tailWord_7506025
  simp only [CollatzResearch.WordTrace]
  refine ⟨273767222631960826855687529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182511481754640551237125019 273767222631960826855687529)
  ·
    refine ⟨205325416973970620141765647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273767222631960826855687529 205325416973970620141765647)
    ·
      refine ⟨307988125460955930212648471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205325416973970620141765647 307988125460955930212648471)
      ·
        refine ⟨461982188191433895318972707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307988125460955930212648471 461982188191433895318972707)
        ·
          refine ⟨692973282287150842978459061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461982188191433895318972707 692973282287150842978459061)
          ·
            refine ⟨64966245214420391529230537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 692973282287150842978459061 64966245214420391529230537)
            ·
              refine ⟨48724683910815293646922903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64966245214420391529230537 48724683910815293646922903)
              ·
                refine ⟨73087025866222940470384355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48724683910815293646922903 73087025866222940470384355)
                ·
                  refine ⟨109630538799334410705576533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73087025866222940470384355 109630538799334410705576533)
                  ·
                    refine ⟨1284732876554700125455975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109630538799334410705576533 1284732876554700125455975)
                    ·
                      rfl

theorem cell23_7506025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_7506025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506025 prefixEnd_7506025 := by exact prefixLift 7506025
  have htrace : WordTrace (prefixWord ++ tailWord_7506025) baseStart_7506025 baseEnd_7506025 := by
    simpa [prefixWord, tailWord_7506025, baseEnd_7506025] using wordTrace_append hprefix tailTrace_7506025
  have hstable : (prefixWord ++ tailWord_7506025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506025).length < 2 ^ (prefixWord ++ tailWord_7506025).sum := by decide
  have hdescent : baseEnd_7506025 < baseStart_7506025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506052 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_7506052 : Nat := 118140960795 + 7506052 * 2 ^ 59
def prefixEnd_7506052 : Nat := 4983230072969 + 3 ^ 40 * 7506052 * 2
def baseEnd_7506052 : Nat := 3854212493641771770730301

theorem tailTrace_7506052 : CollatzResearch.WordTrace tailWord_7506052 prefixEnd_7506052 3854212493641771770730301 := by
  unfold tailWord_7506052
  simp only [CollatzResearch.WordTrace]
  refine ⟨136884103701431505233460205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182512138268575340311280273 136884103701431505233460205)
  ·
    refine ⟨51331538888036814462547577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136884103701431505233460205 51331538888036814462547577)
    ·
      refine ⟨38498654166027610846910683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51331538888036814462547577 38498654166027610846910683)
      ·
        refine ⟨57747981249041416270366025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38498654166027610846910683 57747981249041416270366025)
        ·
          refine ⟨43310985936781062202774519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57747981249041416270366025 43310985936781062202774519)
          ·
            refine ⟨64966478905171593304161779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43310985936781062202774519 64966478905171593304161779)
            ·
              refine ⟨97449718357757389956242669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64966478905171593304161779 97449718357757389956242669)
              ·
                refine ⟨36543644384159021233591001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97449718357757389956242669 36543644384159021233591001)
                ·
                  refine ⟨27407733288119265925193251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36543644384159021233591001 27407733288119265925193251)
                  ·
                    refine ⟨41111599932178898887789877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27407733288119265925193251 41111599932178898887789877)
                    ·
                      refine ⟨3854212493641771770730301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41111599932178898887789877 3854212493641771770730301)
                      ·
                        rfl

theorem cell23_7506052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_7506052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506052 prefixEnd_7506052 := by exact prefixLift 7506052
  have htrace : WordTrace (prefixWord ++ tailWord_7506052) baseStart_7506052 baseEnd_7506052 := by
    simpa [prefixWord, tailWord_7506052, baseEnd_7506052] using wordTrace_append hprefix tailTrace_7506052
  have hstable : (prefixWord ++ tailWord_7506052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506052).length < 2 ^ (prefixWord ++ tailWord_7506052).sum := by decide
  have hdescent : baseEnd_7506052 < baseStart_7506052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506053 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 1, 3, 2]
def baseStart_7506053 : Nat := 118140960795 + 7506053 * 2 ^ 59
def prefixEnd_7506053 : Nat := 4983230072969 + 3 ^ 40 * 7506053 * 2
def baseEnd_7506053 : Nat := 3854213007122426266817797

theorem tailTrace_7506053 : CollatzResearch.WordTrace tailWord_7506053 prefixEnd_7506053 3854213007122426266817797 := by
  unfold tailWord_7506053
  simp only [CollatzResearch.WordTrace]
  refine ⟨273768243875859387637706813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182512162583906258425137875 273768243875859387637706813)
  ·
    refine ⟨102663091453447270364140055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273768243875859387637706813 102663091453447270364140055)
    ·
      refine ⟨153994637180170905546210083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102663091453447270364140055 153994637180170905546210083)
      ·
        refine ⟨230991955770256358319315125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153994637180170905546210083 230991955770256358319315125)
        ·
          refine ⟨21655495853461533592435793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230991955770256358319315125 21655495853461533592435793)
          ·
            refine ⟨16241621890096150194326845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21655495853461533592435793 16241621890096150194326845)
            ·
              refine ⟨6090608208786056322872567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16241621890096150194326845 6090608208786056322872567)
              ·
                refine ⟨9135912313179084484308851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090608208786056322872567 9135912313179084484308851)
                ·
                  refine ⟨13703868469768626726463277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9135912313179084484308851 13703868469768626726463277)
                  ·
                    refine ⟨5138950676163235022423729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13703868469768626726463277 5138950676163235022423729)
                    ·
                      refine ⟨3854213007122426266817797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5138950676163235022423729 3854213007122426266817797)
                      ·
                        rfl

theorem cell23_7506053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_7506053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506053 prefixEnd_7506053 := by exact prefixLift 7506053
  have htrace : WordTrace (prefixWord ++ tailWord_7506053) baseStart_7506053 baseEnd_7506053 := by
    simpa [prefixWord, tailWord_7506053, baseEnd_7506053] using wordTrace_append hprefix tailTrace_7506053
  have hstable : (prefixWord ++ tailWord_7506053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506053).length < 2 ^ (prefixWord ++ tailWord_7506053).sum := by decide
  have hdescent : baseEnd_7506053 < baseStart_7506053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506079 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7506079 : Nat := 118140960795 + 7506079 * 2 ^ 59
def prefixEnd_7506079 : Nat := 4983230072969 + 3 ^ 40 * 7506079 * 2
def baseEnd_7506079 : Nat := 3854226357619443165092677

theorem tailTrace_7506079 : CollatzResearch.WordTrace tailWord_7506079 prefixEnd_7506079 3854226357619443165092677 := by
  unfold tailWord_7506079
  simp only [CollatzResearch.WordTrace]
  refine ⟨273769192173765194078153291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182512794782510129385435527 273769192173765194078153291)
  ·
    refine ⟨410653788260647791117229937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273769192173765194078153291 410653788260647791117229937)
    ·
      refine ⟨307990341195485843337922453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410653788260647791117229937 307990341195485843337922453)
      ·
        refine ⟨14437047243538398906465115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 307990341195485843337922453 14437047243538398906465115)
        ·
          refine ⟨21655570865307598359697673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14437047243538398906465115 21655570865307598359697673)
          ·
            refine ⟨16241678148980698769773255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21655570865307598359697673 16241678148980698769773255)
            ·
              refine ⟨24362517223471048154659883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16241678148980698769773255 24362517223471048154659883)
              ·
                refine ⟨36543775835206572231989825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24362517223471048154659883 36543775835206572231989825)
                ·
                  refine ⟨27407831876404929173992369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36543775835206572231989825 27407831876404929173992369)
                  ·
                    refine ⟨20555873907303696880494277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27407831876404929173992369 20555873907303696880494277)
                    ·
                      refine ⟨3854226357619443165092677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20555873907303696880494277 3854226357619443165092677)
                      ·
                        rfl

theorem cell23_7506079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7506079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506079 prefixEnd_7506079 := by exact prefixLift 7506079
  have htrace : WordTrace (prefixWord ++ tailWord_7506079) baseStart_7506079 baseEnd_7506079 := by
    simpa [prefixWord, tailWord_7506079, baseEnd_7506079] using wordTrace_append hprefix tailTrace_7506079
  have hstable : (prefixWord ++ tailWord_7506079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506079).length < 2 ^ (prefixWord ++ tailWord_7506079).sum := by decide
  have hdescent : baseEnd_7506079 < baseStart_7506079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506159 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 3]
def baseStart_7506159 : Nat := 118140960795 + 7506159 * 2 ^ 59
def prefixEnd_7506159 : Nat := 4983230072969 + 3 ^ 40 * 7506159 * 2
def baseEnd_7506159 : Nat := 3854267436071802852092309

theorem tailTrace_7506159 : CollatzResearch.WordTrace tailWord_7506159 prefixEnd_7506159 3854267436071802852092309 := by
  unfold tailWord_7506159
  simp only [CollatzResearch.WordTrace]
  refine ⟨273772110013475367741065531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182514740008983578494043687 273772110013475367741065531)
  ·
    refine ⟨410658165020213051611598297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273772110013475367741065531 410658165020213051611598297)
    ·
      refine ⟨307993623765159788708698723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410658165020213051611598297 307993623765159788708698723)
      ·
        refine ⟨461990435647739683063048085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307993623765159788708698723 461990435647739683063048085)
        ·
          refine ⟨21655801670987797643580379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 461990435647739683063048085 21655801670987797643580379)
          ·
            refine ⟨32483702506481696465370569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21655801670987797643580379 32483702506481696465370569)
            ·
              refine ⟨24362776879861272349027927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32483702506481696465370569 24362776879861272349027927)
              ·
                refine ⟨36544165319791908523541891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24362776879861272349027927 36544165319791908523541891)
                ·
                  refine ⟨54816247979687862785312837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36544165319791908523541891 54816247979687862785312837)
                  ·
                    refine ⟨10278046496191474272246157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54816247979687862785312837 10278046496191474272246157)
                    ·
                      refine ⟨3854267436071802852092309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10278046496191474272246157 3854267436071802852092309)
                      ·
                        rfl

theorem cell23_7506159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_7506159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506159 prefixEnd_7506159 := by exact prefixLift 7506159
  have htrace : WordTrace (prefixWord ++ tailWord_7506159) baseStart_7506159 baseEnd_7506159 := by
    simpa [prefixWord, tailWord_7506159, baseEnd_7506159] using wordTrace_append hprefix tailTrace_7506159
  have hstable : (prefixWord ++ tailWord_7506159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506159).length < 2 ^ (prefixWord ++ tailWord_7506159).sum := by decide
  have hdescent : baseEnd_7506159 < baseStart_7506159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506233 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7506233 : Nat := 118140960795 + 7506233 * 2 ^ 59
def prefixEnd_7506233 : Nat := 4983230072969 + 3 ^ 40 * 7506233 * 2
def baseEnd_7506233 : Nat := 3854305433640235562566969

theorem tailTrace_7506233 : CollatzResearch.WordTrace tailWord_7506233 prefixEnd_7506233 3854305433640235562566969 := by
  unfold tailWord_7506233
  simp only [CollatzResearch.WordTrace]
  refine ⟨273774809015207278379259353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182516539343471518919506235 273774809015207278379259353)
  ·
    refine ⟨205331106761405458784444515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273774809015207278379259353 205331106761405458784444515)
    ·
      refine ⟨307996660142108188176666773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205331106761405458784444515 307996660142108188176666773)
      ·
        refine ⟨14437343444161321320781255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 307996660142108188176666773 14437343444161321320781255)
        ·
          refine ⟨21656015166241981981171883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14437343444161321320781255 21656015166241981981171883)
          ·
            refine ⟨32484022749362972971757825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21656015166241981981171883 32484022749362972971757825)
            ·
              refine ⟨24363017062022229728818369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32484022749362972971757825 24363017062022229728818369)
              ·
                refine ⟨18272262796516672296613777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24363017062022229728818369 18272262796516672296613777)
                ·
                  refine ⟨13704197097387504222460333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18272262796516672296613777 13704197097387504222460333)
                  ·
                    refine ⟨5139073911520314083422625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13704197097387504222460333 5139073911520314083422625)
                    ·
                      refine ⟨3854305433640235562566969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139073911520314083422625 3854305433640235562566969)
                      ·
                        rfl

theorem cell23_7506233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7506233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506233 prefixEnd_7506233 := by exact prefixLift 7506233
  have htrace : WordTrace (prefixWord ++ tailWord_7506233) baseStart_7506233 baseEnd_7506233 := by
    simpa [prefixWord, tailWord_7506233, baseEnd_7506233] using wordTrace_append hprefix tailTrace_7506233
  have hstable : (prefixWord ++ tailWord_7506233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506233).length < 2 ^ (prefixWord ++ tailWord_7506233).sum := by decide
  have hdescent : baseEnd_7506233 < baseStart_7506233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506256 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 2, 4]
def baseStart_7506256 : Nat := 118140960795 + 7506256 * 2 ^ 59
def prefixEnd_7506256 : Nat := 4983230072969 + 3 ^ 40 * 7506256 * 2
def baseEnd_7506256 : Nat := 1284772414565096324193121

theorem tailTrace_7506256 : CollatzResearch.WordTrace tailWord_7506256 prefixEnd_7506256 1284772414565096324193121 := by
  unfold tailWord_7506256
  simp only [CollatzResearch.WordTrace]
  refine ⟨136887823947061976653673311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182517098596082635538231081 136887823947061976653673311)
  ·
    refine ⟨205331735920592964980509967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136887823947061976653673311 205331735920592964980509967)
    ·
      refine ⟨307997603880889447470764951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205331735920592964980509967 307997603880889447470764951)
      ·
        refine ⟨461996405821334171206147427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307997603880889447470764951 461996405821334171206147427)
        ·
          refine ⟨692994608732001256809221141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461996405821334171206147427 692994608732001256809221141)
          ·
            refine ⟨32484122284312558912932241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 692994608732001256809221141 32484122284312558912932241)
            ·
              refine ⟨24363091713234419184699181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32484122284312558912932241 24363091713234419184699181)
              ·
                refine ⟨9136159392462907194262193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24363091713234419184699181 9136159392462907194262193)
                ·
                  refine ⟨6852119544347180395696645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9136159392462907194262193 6852119544347180395696645)
                  ·
                    refine ⟨1284772414565096324193121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6852119544347180395696645 1284772414565096324193121)
                    ·
                      rfl

theorem cell23_7506256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 4].length) (baseStart_7506256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506256 prefixEnd_7506256 := by exact prefixLift 7506256
  have htrace : WordTrace (prefixWord ++ tailWord_7506256) baseStart_7506256 baseEnd_7506256 := by
    simpa [prefixWord, tailWord_7506256, baseEnd_7506256] using wordTrace_append hprefix tailTrace_7506256
  have hstable : (prefixWord ++ tailWord_7506256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506256).length < 2 ^ (prefixWord ++ tailWord_7506256).sum := by decide
  have hdescent : baseEnd_7506256 < baseStart_7506256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506263 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 3, 2, 2]
def baseStart_7506263 : Nat := 118140960795 + 7506263 * 2 ^ 59
def prefixEnd_7506263 : Nat := 4983230072969 + 3 ^ 40 * 7506263 * 2
def baseEnd_7506263 : Nat := 3854320838059870445191831

theorem tailTrace_7506263 : CollatzResearch.WordTrace tailWord_7506263 prefixEnd_7506263 3854320838059870445191831 := by
  unfold tailWord_7506263
  simp only [CollatzResearch.WordTrace]
  refine ⟨273775903205098593502851443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182517268803399062335234295 273775903205098593502851443)
  ·
    refine ⟨410663854807647890254277165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273775903205098593502851443 410663854807647890254277165)
    ·
      refine ⟨153998945552867958845353937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410663854807647890254277165 153998945552867958845353937)
      ·
        refine ⟨115499209164650969134015453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153998945552867958845353937 115499209164650969134015453)
        ·
          refine ⟨43312203436744113425255795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115499209164650969134015453 43312203436744113425255795)
          ·
            refine ⟨64968305155116170137883693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43312203436744113425255795 64968305155116170137883693)
            ·
              refine ⟨24363114433168563801706385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64968305155116170137883693 24363114433168563801706385)
              ·
                refine ⟨18272335824876422851279789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24363114433168563801706385 18272335824876422851279789)
                ·
                  refine ⟨6852125934328658569229921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18272335824876422851279789 6852125934328658569229921)
                  ·
                    refine ⟨5139094450746493926922441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6852125934328658569229921 5139094450746493926922441)
                    ·
                      refine ⟨3854320838059870445191831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139094450746493926922441 3854320838059870445191831)
                      ·
                        rfl

theorem cell23_7506263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_7506263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506263 prefixEnd_7506263 := by exact prefixLift 7506263
  have htrace : WordTrace (prefixWord ++ tailWord_7506263) baseStart_7506263 baseEnd_7506263 := by
    simpa [prefixWord, tailWord_7506263, baseEnd_7506263] using wordTrace_append hprefix tailTrace_7506263
  have hstable : (prefixWord ++ tailWord_7506263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506263).length < 2 ^ (prefixWord ++ tailWord_7506263).sum := by decide
  have hdescent : baseEnd_7506263 < baseStart_7506263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506266 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3]
def baseStart_7506266 : Nat := 118140960795 + 7506266 * 2 ^ 59
def prefixEnd_7506266 : Nat := 4983230072969 + 3 ^ 40 * 7506266 * 2
def baseEnd_7506266 : Nat := 3854322378501833933454317

theorem tailTrace_7506266 : CollatzResearch.WordTrace tailWord_7506266 prefixEnd_7506266 3854322378501833933454317 := by
  unfold tailWord_7506266
  simp only [CollatzResearch.WordTrace]
  refine ⟨68444003156021931253802663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182517341749391816676807101 68444003156021931253802663)
  ·
    refine ⟨102666004734032896880703995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68444003156021931253802663 102666004734032896880703995)
    ·
      refine ⟨153999007101049345321055993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102666004734032896880703995 153999007101049345321055993)
      ·
        refine ⟨115499255325787008990791995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153999007101049345321055993 115499255325787008990791995)
        ·
          refine ⟨173248882988680513486187993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115499255325787008990791995 173248882988680513486187993)
          ·
            refine ⟨129936662241510385114640995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173248882988680513486187993 129936662241510385114640995)
            ·
              refine ⟨194904993362265577671961493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129936662241510385114640995 194904993362265577671961493)
              ·
                refine ⟨9136171563856198953373195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194904993362265577671961493 9136171563856198953373195)
                ·
                  refine ⟨13704257345784298430059793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9136171563856198953373195 13704257345784298430059793)
                  ·
                    refine ⟨10278193009338223822544845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13704257345784298430059793 10278193009338223822544845)
                    ·
                      refine ⟨3854322378501833933454317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10278193009338223822544845 3854322378501833933454317)
                      ·
                        rfl

theorem cell23_7506266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_7506266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506266 prefixEnd_7506266 := by exact prefixLift 7506266
  have htrace : WordTrace (prefixWord ++ tailWord_7506266) baseStart_7506266 baseEnd_7506266 := by
    simpa [prefixWord, tailWord_7506266, baseEnd_7506266] using wordTrace_append hprefix tailTrace_7506266
  have hstable : (prefixWord ++ tailWord_7506266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506266).length < 2 ^ (prefixWord ++ tailWord_7506266).sum := by decide
  have hdescent : baseEnd_7506266 < baseStart_7506266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506280 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_7506280 : Nat := 118140960795 + 7506280 * 2 ^ 59
def prefixEnd_7506280 : Nat := 4983230072969 + 3 ^ 40 * 7506280 * 2
def baseEnd_7506280 : Nat := 3854329567230996878679253

theorem tailTrace_7506280 : CollatzResearch.WordTrace tailWord_7506280 prefixEnd_7506280 3854329567230996878679253 := by
  unfold tailWord_7506280
  simp only [CollatzResearch.WordTrace]
  refine ⟨136888261623018502703110147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182517682164024670270813529 136888261623018502703110147)
  ·
    refine ⟨205332392434527754054665221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136888261623018502703110147 205332392434527754054665221)
    ·
      refine ⟨38499823581473953885249729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205332392434527754054665221 38499823581473953885249729)
      ·
        refine ⟨28874867686105465413937297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38499823581473953885249729 28874867686105465413937297)
        ·
          refine ⟨21656150764579099060452973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28874867686105465413937297 21656150764579099060452973)
          ·
            refine ⟨8121056536717162147669865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21656150764579099060452973 8121056536717162147669865)
            ·
              refine ⟨6090792402537871610752399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8121056536717162147669865 6090792402537871610752399)
              ·
                refine ⟨9136188603806807416128599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090792402537871610752399 9136188603806807416128599)
                ·
                  refine ⟨13704282905710211124192899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9136188603806807416128599 13704282905710211124192899)
                  ·
                    refine ⟨20556424358565316686289349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13704282905710211124192899 20556424358565316686289349)
                    ·
                      refine ⟨3854329567230996878679253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20556424358565316686289349 3854329567230996878679253)
                      ·
                        rfl

theorem cell23_7506280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_7506280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506280 prefixEnd_7506280 := by exact prefixLift 7506280
  have htrace : WordTrace (prefixWord ++ tailWord_7506280) baseStart_7506280 baseEnd_7506280 := by
    simpa [prefixWord, tailWord_7506280, baseEnd_7506280] using wordTrace_append hprefix tailTrace_7506280
  have hstable : (prefixWord ++ tailWord_7506280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506280).length < 2 ^ (prefixWord ++ tailWord_7506280).sum := by decide
  have hdescent : baseEnd_7506280 < baseStart_7506280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506313 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 3]
def baseStart_7506313 : Nat := 118140960795 + 7506313 * 2 ^ 59
def prefixEnd_7506313 : Nat := 4983230072969 + 3 ^ 40 * 7506313 * 2
def baseEnd_7506313 : Nat := 3854346512092595249566601

theorem tailTrace_7506313 : CollatzResearch.WordTrace tailWord_7506313 prefixEnd_7506313 3854346512092595249566601 := by
  unfold tailWord_7506313
  simp only [CollatzResearch.WordTrace]
  refine ⟨273777726854917452042171593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182518484569944968028114395 273777726854917452042171593)
  ·
    refine ⟨205333295141188089031628695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273777726854917452042171593 205333295141188089031628695)
    ·
      refine ⟨307999942711782133547443043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205333295141188089031628695 307999942711782133547443043)
      ·
        refine ⟨461999914067673200321164565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307999942711782133547443043 461999914067673200321164565)
        ·
          refine ⟨21656245971922181265054589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 461999914067673200321164565 21656245971922181265054589)
          ·
            refine ⟨8121092239470817974395471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21656245971922181265054589 8121092239470817974395471)
            ·
              refine ⟨12181638359206226961593207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8121092239470817974395471 12181638359206226961593207)
              ·
                refine ⟨18272457538809340442389811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12181638359206226961593207 18272457538809340442389811)
                ·
                  refine ⟨27408686308214010663584717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18272457538809340442389811 27408686308214010663584717)
                  ·
                    refine ⟨10278257365580253998844269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27408686308214010663584717 10278257365580253998844269)
                    ·
                      refine ⟨3854346512092595249566601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10278257365580253998844269 3854346512092595249566601)
                      ·
                        rfl

theorem cell23_7506313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 3].length) (baseStart_7506313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506313 prefixEnd_7506313 := by exact prefixLift 7506313
  have htrace : WordTrace (prefixWord ++ tailWord_7506313) baseStart_7506313 baseEnd_7506313 := by
    simpa [prefixWord, tailWord_7506313, baseEnd_7506313] using wordTrace_append hprefix tailTrace_7506313
  have hstable : (prefixWord ++ tailWord_7506313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506313).length < 2 ^ (prefixWord ++ tailWord_7506313).sum := by decide
  have hdescent : baseEnd_7506313 < baseStart_7506313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506339 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 5]
def baseStart_7506339 : Nat := 118140960795 + 7506339 * 2 ^ 59
def prefixEnd_7506339 : Nat := 4983230072969 + 3 ^ 40 * 7506339 * 2
def baseEnd_7506339 : Nat := 3854359862589612147841481

theorem tailTrace_7506339 : CollatzResearch.WordTrace tailWord_7506339 prefixEnd_7506339 3854359862589612147841481 := by
  unfold tailWord_7506339
  simp only [CollatzResearch.WordTrace]
  refine ⟨273778675152823258482618071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182519116768548838988412047 273778675152823258482618071)
  ·
    refine ⟨410668012729234887723927107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273778675152823258482618071 410668012729234887723927107)
    ·
      refine ⟨616002019093852331585890661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410668012729234887723927107 616002019093852331585890661)
      ·
        refine ⟨115500378580097312172354499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 616002019093852331585890661 115500378580097312172354499)
        ·
          refine ⟨173250567870145968258531749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115500378580097312172354499 173250567870145968258531749)
          ·
            refine ⟨32484481475652369048474703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173250567870145968258531749 32484481475652369048474703)
            ·
              refine ⟨48726722213478553572712055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32484481475652369048474703 48726722213478553572712055)
              ·
                refine ⟨73090083320217830359068083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48726722213478553572712055 73090083320217830359068083)
                ·
                  refine ⟨109635124980326745538602125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73090083320217830359068083 109635124980326745538602125)
                  ·
                    refine ⟨41113171867622529576975797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109635124980326745538602125 41113171867622529576975797)
                    ·
                      refine ⟨3854359862589612147841481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41113171867622529576975797 3854359862589612147841481)
                      ·
                        rfl

theorem cell23_7506339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_7506339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506339 prefixEnd_7506339 := by exact prefixLift 7506339
  have htrace : WordTrace (prefixWord ++ tailWord_7506339) baseStart_7506339 baseEnd_7506339 := by
    simpa [prefixWord, tailWord_7506339, baseEnd_7506339] using wordTrace_append hprefix tailTrace_7506339
  have hstable : (prefixWord ++ tailWord_7506339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506339).length < 2 ^ (prefixWord ++ tailWord_7506339).sum := by decide
  have hdescent : baseEnd_7506339 < baseStart_7506339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506366 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_7506366 : Nat := 118140960795 + 7506366 * 2 ^ 59
def prefixEnd_7506366 : Nat := 4983230072969 + 3 ^ 40 * 7506366 * 2
def baseEnd_7506366 : Nat := 3854373726567283542203857

theorem tailTrace_7506366 : CollatzResearch.WordTrace tailWord_7506366 prefixEnd_7506366 3854373726567283542203857 := by
  unfold tailWord_7506366
  simp only [CollatzResearch.WordTrace]
  refine ⟨34222457490465680261731369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182519773282483628062567301 34222457490465680261731369)
  ·
    refine ⟨25666843117849260196298527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34222457490465680261731369 25666843117849260196298527)
    ·
      refine ⟨38500264676773890294447791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25666843117849260196298527 38500264676773890294447791)
      ·
        refine ⟨57750397015160835441671687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38500264676773890294447791 57750397015160835441671687)
        ·
          refine ⟨86625595522741253162507531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57750397015160835441671687 86625595522741253162507531)
          ·
            refine ⟨129938393284111879743761297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86625595522741253162507531 129938393284111879743761297)
            ·
              refine ⟨97453794963083909807820973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129938393284111879743761297 97453794963083909807820973)
              ·
                refine ⟨36545173111156466177932865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97453794963083909807820973 36545173111156466177932865)
                ·
                  refine ⟨27408879833367349633449649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36545173111156466177932865 27408879833367349633449649)
                  ·
                    refine ⟨20556659875025512225087237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27408879833367349633449649 20556659875025512225087237)
                    ·
                      refine ⟨3854373726567283542203857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20556659875025512225087237 3854373726567283542203857)
                      ·
                        rfl

theorem cell23_7506366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_7506366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506366 prefixEnd_7506366 := by exact prefixLift 7506366
  have htrace : WordTrace (prefixWord ++ tailWord_7506366) baseStart_7506366 baseEnd_7506366 := by
    simpa [prefixWord, tailWord_7506366, baseEnd_7506366] using wordTrace_append hprefix tailTrace_7506366
  have hstable : (prefixWord ++ tailWord_7506366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506366).length < 2 ^ (prefixWord ++ tailWord_7506366).sum := by decide
  have hdescent : baseEnd_7506366 < baseStart_7506366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506410 : List Nat := [3, 1, 3, 1, 3, 1, 4, 2, 5]
def baseStart_7506410 : Nat := 118140960795 + 7506410 * 2 ^ 59
def prefixEnd_7506410 : Nat := 4983230072969 + 3 ^ 40 * 7506410 * 2
def baseEnd_7506410 : Nat := 428266257746231263339295

theorem tailTrace_7506410 : CollatzResearch.WordTrace tailWord_7506410 prefixEnd_7506410 428266257746231263339295 := by
  unfold tailWord_7506410
  simp only [CollatzResearch.WordTrace]
  refine ⟨68445316183891509402113171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182520843157044025072301789 68445316183891509402113171)
  ·
    refine ⟨102667974275837264103169757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68445316183891509402113171 102667974275837264103169757)
    ·
      refine ⟨38500490353438974038688659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102667974275837264103169757 38500490353438974038688659)
      ·
        refine ⟨57750735530158461058032989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38500490353438974038688659 57750735530158461058032989)
        ·
          refine ⟨21656525823809422896762371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57750735530158461058032989 21656525823809422896762371)
          ·
            refine ⟨32484788735714134345143557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21656525823809422896762371 32484788735714134345143557)
            ·
              refine ⟨6090897887946400189714417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32484788735714134345143557 6090897887946400189714417)
              ·
                refine ⟨4568173415959800142285813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6090897887946400189714417 4568173415959800142285813)
                ·
                  refine ⟨428266257746231263339295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4568173415959800142285813 428266257746231263339295)
                  ·
                    rfl

theorem cell23_7506410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_7506410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506410 prefixEnd_7506410 := by exact prefixLift 7506410
  have htrace : WordTrace (prefixWord ++ tailWord_7506410) baseStart_7506410 baseEnd_7506410 := by
    simpa [prefixWord, tailWord_7506410, baseEnd_7506410] using wordTrace_append hprefix tailTrace_7506410
  have hstable : (prefixWord ++ tailWord_7506410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506410).length < 2 ^ (prefixWord ++ tailWord_7506410).sum := by decide
  have hdescent : baseEnd_7506410 < baseStart_7506410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506443 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 4]
def baseStart_7506443 : Nat := 118140960795 + 7506443 * 2 ^ 59
def prefixEnd_7506443 : Nat := 4983230072969 + 3 ^ 40 * 7506443 * 2
def baseEnd_7506443 : Nat := 3854413264577679740941003

theorem tailTrace_7506443 : CollatzResearch.WordTrace tailWord_7506443 prefixEnd_7506443 3854413264577679740941003 := by
  unfold tailWord_7506443
  simp only [CollatzResearch.WordTrace]
  refine ⟨273782468344446484244403983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182521645562964322829602655 273782468344446484244403983)
  ·
    refine ⟨410673702516669726366605975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273782468344446484244403983 410673702516669726366605975)
    ·
      refine ⟨616010553775004589549908963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410673702516669726366605975 616010553775004589549908963)
      ·
        refine ⟨924015830662506884324863445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616010553775004589549908963 924015830662506884324863445)
        ·
          refine ⟨21656621031152505101363987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 924015830662506884324863445 21656621031152505101363987)
          ·
            refine ⟨32484931546728757652045981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21656621031152505101363987 32484931546728757652045981)
            ·
              refine ⟨12181849330023284119517243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32484931546728757652045981 12181849330023284119517243)
              ·
                refine ⟨18272773995034926179275865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12181849330023284119517243 18272773995034926179275865)
                ·
                  refine ⟨13704580496276194634456899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18272773995034926179275865 13704580496276194634456899)
                  ·
                    refine ⟨20556870744414291951685349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13704580496276194634456899 20556870744414291951685349)
                    ·
                      refine ⟨3854413264577679740941003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20556870744414291951685349 3854413264577679740941003)
                      ·
                        rfl

theorem cell23_7506443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 4].length) (baseStart_7506443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506443 prefixEnd_7506443 := by exact prefixLift 7506443
  have htrace : WordTrace (prefixWord ++ tailWord_7506443) baseStart_7506443 baseEnd_7506443 := by
    simpa [prefixWord, tailWord_7506443, baseEnd_7506443] using wordTrace_append hprefix tailTrace_7506443
  have hstable : (prefixWord ++ tailWord_7506443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506443).length < 2 ^ (prefixWord ++ tailWord_7506443).sum := by decide
  have hdescent : baseEnd_7506443 < baseStart_7506443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506456 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_7506456 : Nat := 118140960795 + 7506456 * 2 ^ 59
def prefixEnd_7506456 : Nat := 4983230072969 + 3 ^ 40 * 7506456 * 2
def baseEnd_7506456 : Nat := 3854419939826188190078443

theorem tailTrace_7506456 : CollatzResearch.WordTrace tailWord_7506456 prefixEnd_7506456 3854419939826188190078443 := by
  unfold tailWord_7506456
  simp only [CollatzResearch.WordTrace]
  refine ⟨136891471246699693732313611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182521961662266258309751481 136891471246699693732313611)
  ·
    refine ⟨205337206870049540598470417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136891471246699693732313611 205337206870049540598470417)
    ·
      refine ⟨154002905152537155448852813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205337206870049540598470417 154002905152537155448852813)
      ·
        refine ⟨57751089432201433293319805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154002905152537155448852813 57751089432201433293319805)
        ·
          refine ⟨21656658537075537484994927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57751089432201433293319805 21656658537075537484994927)
          ·
            refine ⟨32484987805613306227492391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21656658537075537484994927 32484987805613306227492391)
            ·
              refine ⟨48727481708419959341238587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32484987805613306227492391 48727481708419959341238587)
              ·
                refine ⟨73091222562629939011857881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48727481708419959341238587 73091222562629939011857881)
                ·
                  refine ⟨54818416921972454258893411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73091222562629939011857881 54818416921972454258893411)
                  ·
                    refine ⟨82227625382958681388340117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54818416921972454258893411 82227625382958681388340117)
                    ·
                      refine ⟨3854419939826188190078443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82227625382958681388340117 3854419939826188190078443)
                      ·
                        rfl

theorem cell23_7506456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_7506456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506456 prefixEnd_7506456 := by exact prefixLift 7506456
  have htrace : WordTrace (prefixWord ++ tailWord_7506456) baseStart_7506456 baseEnd_7506456 := by
    simpa [prefixWord, tailWord_7506456, baseEnd_7506456] using wordTrace_append hprefix tailTrace_7506456
  have hstable : (prefixWord ++ tailWord_7506456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506456).length < 2 ^ (prefixWord ++ tailWord_7506456).sum := by decide
  have hdescent : baseEnd_7506456 < baseStart_7506456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506459 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 7]
def baseStart_7506459 : Nat := 118140960795 + 7506459 * 2 ^ 59
def prefixEnd_7506459 : Nat := 4983230072969 + 3 ^ 40 * 7506459 * 2
def baseEnd_7506459 : Nat := 3854421480268151678340929

theorem tailTrace_7506459 : CollatzResearch.WordTrace tailWord_7506459 prefixEnd_7506459 3854421480268151678340929 := by
  unfold tailWord_7506459
  simp only [CollatzResearch.WordTrace]
  refine ⟨273783051912388518976986431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182522034608259012651324287 273783051912388518976986431)
  ·
    refine ⟨410674577868582778465479647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273783051912388518976986431 410674577868582778465479647)
    ·
      refine ⟨616011866802874167698219471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410674577868582778465479647 616011866802874167698219471)
      ·
        refine ⟨924017800204311251547329207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616011866802874167698219471 924017800204311251547329207)
        ·
          refine ⟨1386026700306466877320993811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924017800204311251547329207 1386026700306466877320993811)
          ·
            refine ⟨2079040050459700315981490717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386026700306466877320993811 2079040050459700315981490717)
            ·
              refine ⟨779640018922387618493059019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2079040050459700315981490717 779640018922387618493059019)
              ·
                refine ⟨1169460028383581427739588529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779640018922387618493059019 1169460028383581427739588529)
                ·
                  refine ⟨877095021287686070804691397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1169460028383581427739588529 877095021287686070804691397)
                  ·
                    refine ⟨164455316491441138275879637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 877095021287686070804691397 164455316491441138275879637)
                    ·
                      refine ⟨3854421480268151678340929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164455316491441138275879637 3854421480268151678340929)
                      ·
                        rfl

theorem cell23_7506459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_7506459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506459 prefixEnd_7506459 := by exact prefixLift 7506459
  have htrace : WordTrace (prefixWord ++ tailWord_7506459) baseStart_7506459 baseEnd_7506459 := by
    simpa [prefixWord, tailWord_7506459, baseEnd_7506459] using wordTrace_append hprefix tailTrace_7506459
  have hstable : (prefixWord ++ tailWord_7506459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506459).length < 2 ^ (prefixWord ++ tailWord_7506459).sum := by decide
  have hdescent : baseEnd_7506459 < baseStart_7506459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506483 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 6]
def baseStart_7506483 : Nat := 118140960795 + 7506483 * 2 ^ 59
def prefixEnd_7506483 : Nat := 4983230072969 + 3 ^ 40 * 7506483 * 2
def baseEnd_7506483 : Nat := 428270422644873287160091

theorem tailTrace_7506483 : CollatzResearch.WordTrace tailWord_7506483 prefixEnd_7506483 428270422644873287160091 := by
  unfold tailWord_7506483
  simp only [CollatzResearch.WordTrace]
  refine ⟨273783927264301571075860103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182522618176201047383906735 273783927264301571075860103)
  ·
    refine ⟨410675890896452356613790155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273783927264301571075860103 410675890896452356613790155)
    ·
      refine ⟨616013836344678534920685233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410675890896452356613790155 616013836344678534920685233)
      ·
        refine ⟨462010377258508901190513925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616013836344678534920685233 462010377258508901190513925)
        ·
          refine ⟨86626945735970418973221361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 462010377258508901190513925 86626945735970418973221361)
          ·
            refine ⟨64970209301977814229916021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86626945735970418973221361 64970209301977814229916021)
            ·
              refine ⟨6090957122060420084054627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64970209301977814229916021 6090957122060420084054627)
              ·
                refine ⟨9136435683090630126081941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090957122060420084054627 9136435683090630126081941)
                ·
                  refine ⟨428270422644873287160091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9136435683090630126081941 428270422644873287160091)
                  ·
                    rfl

theorem cell23_7506483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 6].length) (baseStart_7506483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506483 prefixEnd_7506483 := by exact prefixLift 7506483
  have htrace : WordTrace (prefixWord ++ tailWord_7506483) baseStart_7506483 baseEnd_7506483 := by
    simpa [prefixWord, tailWord_7506483, baseEnd_7506483] using wordTrace_append hprefix tailTrace_7506483
  have hstable : (prefixWord ++ tailWord_7506483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506483).length < 2 ^ (prefixWord ++ tailWord_7506483).sum := by decide
  have hdescent : baseEnd_7506483 < baseStart_7506483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506496 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 3, 5]
def baseStart_7506496 : Nat := 118140960795 + 7506496 * 2 ^ 59
def prefixEnd_7506496 : Nat := 4983230072969 + 3 ^ 40 * 7506496 * 2
def baseEnd_7506496 : Nat := 1284813493017456011192753

theorem tailTrace_7506496 : CollatzResearch.WordTrace tailWord_7506496 prefixEnd_7506496 1284813493017456011192753 := by
  unfold tailWord_7506496
  simp only [CollatzResearch.WordTrace]
  refine ⟨136892200706627237148041671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182522934275502982864055561 136892200706627237148041671)
  ·
    refine ⟨205338301059940855722062507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136892200706627237148041671 205338301059940855722062507)
    ·
      refine ⟨308007451589911283583093761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205338301059940855722062507 308007451589911283583093761)
      ·
        refine ⟨231005588692433462687320321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308007451589911283583093761 231005588692433462687320321)
        ·
          refine ⟨173254191519325097015490241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231005588692433462687320321 173254191519325097015490241)
          ·
            refine ⟨129940643639493822761617681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173254191519325097015490241 129940643639493822761617681)
            ·
              refine ⟨97455482729620367071213261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129940643639493822761617681 97455482729620367071213261)
              ·
                refine ⟨36545806023607637651704973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97455482729620367071213261 36545806023607637651704973)
                ·
                  refine ⟨13704677258852864119389365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36545806023607637651704973 13704677258852864119389365)
                  ·
                    refine ⟨1284813493017456011192753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13704677258852864119389365 1284813493017456011192753)
                    ·
                      rfl

theorem cell23_7506496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_7506496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506496 prefixEnd_7506496 := by exact prefixLift 7506496
  have htrace : WordTrace (prefixWord ++ tailWord_7506496) baseStart_7506496 baseEnd_7506496 := by
    simpa [prefixWord, tailWord_7506496, baseEnd_7506496] using wordTrace_append hprefix tailTrace_7506496
  have hstable : (prefixWord ++ tailWord_7506496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506496).length < 2 ^ (prefixWord ++ tailWord_7506496).sum := by decide
  have hdescent : baseEnd_7506496 < baseStart_7506496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506513 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 1, 5]
def baseStart_7506513 : Nat := 118140960795 + 7506513 * 2 ^ 59
def prefixEnd_7506513 : Nat := 4983230072969 + 3 ^ 40 * 7506513 * 2
def baseEnd_7506513 : Nat := 1284816402741164822355227

theorem tailTrace_7506513 : CollatzResearch.WordTrace tailWord_7506513 prefixEnd_7506513 1284816402741164822355227 := by
  unfold tailWord_7506513
  simp only [CollatzResearch.WordTrace]
  refine ⟨273785021454192886199452193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182523347636128590799634795 273785021454192886199452193)
  ·
    refine ⟨205338766090644664649589145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273785021454192886199452193 205338766090644664649589145)
    ·
      refine ⟨154004074567983498487191859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205338766090644664649589145 154004074567983498487191859)
      ·
        refine ⟨231006111851975247730787789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154004074567983498487191859 231006111851975247730787789)
        ·
          refine ⟨86627291944490717899045421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231006111851975247730787789 86627291944490717899045421)
          ·
            refine ⟨32485234479184019212142033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86627291944490717899045421 32485234479184019212142033)
            ·
              refine ⟨24363925859388014409106525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32485234479184019212142033 24363925859388014409106525)
              ·
                refine ⟨9136472197270505403414947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24363925859388014409106525 9136472197270505403414947)
                ·
                  refine ⟨13704708295905758105122421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9136472197270505403414947 13704708295905758105122421)
                  ·
                    refine ⟨1284816402741164822355227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13704708295905758105122421 1284816402741164822355227)
                    ·
                      rfl

theorem cell23_7506513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_7506513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506513 prefixEnd_7506513 := by exact prefixLift 7506513
  have htrace : WordTrace (prefixWord ++ tailWord_7506513) baseStart_7506513 baseEnd_7506513 := by
    simpa [prefixWord, tailWord_7506513, baseEnd_7506513] using wordTrace_append hprefix tailTrace_7506513
  have hstable : (prefixWord ++ tailWord_7506513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506513).length < 2 ^ (prefixWord ++ tailWord_7506513).sum := by decide
  have hdescent : baseEnd_7506513 < baseStart_7506513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506556 : List Nat := [2, 2, 2, 1, 1, 2, 4, 9]
def baseStart_7506556 : Nat := 118140960795 + 7506556 * 2 ^ 59
def prefixEnd_7506556 : Nat := 4983230072969 + 3 ^ 40 * 7506556 * 2
def baseEnd_7506556 : Nat := 142758195847838436993629

theorem tailTrace_7506556 : CollatzResearch.WordTrace tailWord_7506556 prefixEnd_7506556 142758195847838436993629 := by
  unfold tailWord_7506556
  simp only [CollatzResearch.WordTrace]
  refine ⟨136893294896518552271633761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182524393195358069695511681 136893294896518552271633761)
  ·
    refine ⟨102669971172388914203725321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136893294896518552271633761 102669971172388914203725321)
    ·
      refine ⟨77002478379291685652793991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102669971172388914203725321 77002478379291685652793991)
      ·
        refine ⟨115503717568937528479190987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77002478379291685652793991 115503717568937528479190987)
        ·
          refine ⟨173255576353406292718786481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115503717568937528479190987 173255576353406292718786481)
          ·
            refine ⟨129941682265054719539089861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173255576353406292718786481 129941682265054719539089861)
            ·
              refine ⟨24364065424697759913579349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129941682265054719539089861 24364065424697759913579349)
              ·
                refine ⟨142758195847838436993629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24364065424697759913579349 142758195847838436993629)
                ·
                  rfl

theorem cell23_7506556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 9].length) (baseStart_7506556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506556 prefixEnd_7506556 := by exact prefixLift 7506556
  have htrace : WordTrace (prefixWord ++ tailWord_7506556) baseStart_7506556 baseEnd_7506556 := by
    simpa [prefixWord, tailWord_7506556, baseEnd_7506556] using wordTrace_append hprefix tailTrace_7506556
  have hstable : (prefixWord ++ tailWord_7506556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506556).length < 2 ^ (prefixWord ++ tailWord_7506556).sum := by decide
  have hdescent : baseEnd_7506556 < baseStart_7506556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506583 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_7506583 : Nat := 118140960795 + 7506583 * 2 ^ 59
def prefixEnd_7506583 : Nat := 4983230072969 + 3 ^ 40 * 7506583 * 2
def baseEnd_7506583 : Nat := 3854485151869309193190359

theorem tailTrace_7506583 : CollatzResearch.WordTrace tailWord_7506583 prefixEnd_7506583 3854485151869309193190359 := by
  unfold tailWord_7506583
  simp only [CollatzResearch.WordTrace]
  refine ⟨273787574563939288154500403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182525049709292858769666935 273787574563939288154500403)
  ·
    refine ⟨410681361845908932231750605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273787574563939288154500403 410681361845908932231750605)
    ·
      refine ⟨154005510692215849586906477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410681361845908932231750605 154005510692215849586906477)
      ·
        refine ⟨57752066509580943595089929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154005510692215849586906477 57752066509580943595089929)
        ·
          refine ⟨43314049882185707696317447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57752066509580943595089929 43314049882185707696317447)
          ·
            refine ⟨64971074823278561544476171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43314049882185707696317447 64971074823278561544476171)
            ·
              refine ⟨97456612234917842316714257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64971074823278561544476171 97456612234917842316714257)
              ·
                refine ⟨73092459176188381737535693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97456612234917842316714257 73092459176188381737535693)
                ·
                  refine ⟨27409672191070643151575885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73092459176188381737535693 27409672191070643151575885)
                  ·
                    refine ⟨10278627071651491181840957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27409672191070643151575885 10278627071651491181840957)
                    ·
                      refine ⟨3854485151869309193190359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10278627071651491181840957 3854485151869309193190359)
                      ·
                        rfl

theorem cell23_7506583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_7506583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506583 prefixEnd_7506583 := by exact prefixLift 7506583
  have htrace : WordTrace (prefixWord ++ tailWord_7506583) baseStart_7506583 baseEnd_7506583 := by
    simpa [prefixWord, tailWord_7506583, baseEnd_7506583] using wordTrace_append hprefix tailTrace_7506583
  have hstable : (prefixWord ++ tailWord_7506583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506583).length < 2 ^ (prefixWord ++ tailWord_7506583).sum := by decide
  have hdescent : baseEnd_7506583 < baseStart_7506583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506584 : List Nat := [2, 1, 2, 4, 1, 1, 3, 4, 1, 2, 2]
def baseStart_7506584 : Nat := 118140960795 + 7506584 * 2 ^ 59
def prefixEnd_7506584 : Nat := 4983230072969 + 3 ^ 40 * 7506584 * 2
def baseEnd_7506584 : Nat := 3854485665349963689277855

theorem tailTrace_7506584 : CollatzResearch.WordTrace tailWord_7506584 prefixEnd_7506584 3854485665349963689277855 := by
  unfold tailWord_7506584
  simp only [CollatzResearch.WordTrace]
  refine ⟨136893805518467832662643403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182525074024623776883524537 136893805518467832662643403)
  ·
    refine ⟨205340708277701748993965105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136893805518467832662643403 205340708277701748993965105)
    ·
      refine ⟨154005531208276311745473829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205340708277701748993965105 154005531208276311745473829)
      ·
        refine ⟨28876037101551808452276343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154005531208276311745473829 28876037101551808452276343)
        ·
          refine ⟨43314055652327712678414515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28876037101551808452276343 43314055652327712678414515)
          ·
            refine ⟨64971083478491569017621773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43314055652327712678414515 64971083478491569017621773)
            ·
              refine ⟨24364156304434338381608165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64971083478491569017621773 24364156304434338381608165)
              ·
                refine ⟨4568279307081438446551531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24364156304434338381608165 4568279307081438446551531)
                ·
                  refine ⟨6852418960622157669827297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568279307081438446551531 6852418960622157669827297)
                  ·
                    refine ⟨5139314220466618252370473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6852418960622157669827297 5139314220466618252370473)
                    ·
                      refine ⟨3854485665349963689277855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139314220466618252370473 3854485665349963689277855)
                      ·
                        rfl

theorem cell23_7506584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_7506584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506584 prefixEnd_7506584 := by exact prefixLift 7506584
  have htrace : WordTrace (prefixWord ++ tailWord_7506584) baseStart_7506584 baseEnd_7506584 := by
    simpa [prefixWord, tailWord_7506584, baseEnd_7506584] using wordTrace_append hprefix tailTrace_7506584
  have hstable : (prefixWord ++ tailWord_7506584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506584).length < 2 ^ (prefixWord ++ tailWord_7506584).sum := by decide
  have hdescent : baseEnd_7506584 < baseStart_7506584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506634 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_7506634 : Nat := 118140960795 + 7506634 * 2 ^ 59
def prefixEnd_7506634 : Nat := 4983230072969 + 3 ^ 40 * 7506634 * 2
def baseEnd_7506634 : Nat := 3854511339382688493652625

theorem tailTrace_7506634 : CollatzResearch.WordTrace tailWord_7506634 prefixEnd_7506634 3854511339382688493652625 := by
  unfold tailWord_7506634
  simp only [CollatzResearch.WordTrace]
  refine ⟨68447358671688630966151739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182526289791169682576404637 68447358671688630966151739)
  ·
    refine ⟨102671038007532946449227609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68447358671688630966151739 102671038007532946449227609)
    ·
      refine ⟨77003278505649709836920707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102671038007532946449227609 77003278505649709836920707)
      ·
        refine ⟨115504917758474564755381061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77003278505649709836920707 115504917758474564755381061)
        ·
          refine ⟨21657172079713980891633949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115504917758474564755381061 21657172079713980891633949)
          ·
            refine ⟨8121439529892742834362731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21657172079713980891633949 8121439529892742834362731)
            ·
              refine ⟨12182159294839114251544097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8121439529892742834362731 12182159294839114251544097)
              ·
                refine ⟨9136619471129335688658073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12182159294839114251544097 9136619471129335688658073)
                ·
                  refine ⟨6852464603347001766493555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9136619471129335688658073 6852464603347001766493555)
                  ·
                    refine ⟨10278696905020502649740333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6852464603347001766493555 10278696905020502649740333)
                    ·
                      refine ⟨3854511339382688493652625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10278696905020502649740333 3854511339382688493652625)
                      ·
                        rfl

theorem cell23_7506634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_7506634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506634 prefixEnd_7506634 := by exact prefixLift 7506634
  have htrace : WordTrace (prefixWord ++ tailWord_7506634) baseStart_7506634 baseEnd_7506634 := by
    simpa [prefixWord, tailWord_7506634, baseEnd_7506634] using wordTrace_append hprefix tailTrace_7506634
  have hstable : (prefixWord ++ tailWord_7506634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506634).length < 2 ^ (prefixWord ++ tailWord_7506634).sum := by decide
  have hdescent : baseEnd_7506634 < baseStart_7506634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506657 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_7506657 : Nat := 118140960795 + 7506657 * 2 ^ 59
def prefixEnd_7506657 : Nat := 4983230072969 + 3 ^ 40 * 7506657 * 2
def baseEnd_7506657 : Nat := 3854523149437741903665019

theorem tailTrace_7506657 : CollatzResearch.WordTrace tailWord_7506657 prefixEnd_7506657 3854523149437741903665019 := by
  unfold tailWord_7506657
  simp only [CollatzResearch.WordTrace]
  refine ⟨273790273565671198792694225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182526849043780799195129483 273790273565671198792694225)
  ·
    refine ⟨205342705174253399094520669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273790273565671198792694225 205342705174253399094520669)
    ·
      refine ⟨77003514440345024660445251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205342705174253399094520669 77003514440345024660445251)
      ·
        refine ⟨115505271660517536990667877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77003514440345024660445251 115505271660517536990667877)
        ·
          refine ⟨21657238436347038185750227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115505271660517536990667877 21657238436347038185750227)
          ·
            refine ⟨32485857654520557278625341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21657238436347038185750227 32485857654520557278625341)
            ·
              refine ⟨12182196620445208979484503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32485857654520557278625341 12182196620445208979484503)
              ·
                refine ⟨18273294930667813469226755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12182196620445208979484503 18273294930667813469226755)
                ·
                  refine ⟨27409942396001720203840133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18273294930667813469226755 27409942396001720203840133)
                  ·
                    refine ⟨5139364199250322538220025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27409942396001720203840133 5139364199250322538220025)
                    ·
                      refine ⟨3854523149437741903665019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139364199250322538220025 3854523149437741903665019)
                      ·
                        rfl

theorem cell23_7506657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_7506657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506657 prefixEnd_7506657 := by exact prefixLift 7506657
  have htrace : WordTrace (prefixWord ++ tailWord_7506657) baseStart_7506657 baseEnd_7506657 := by
    simpa [prefixWord, tailWord_7506657, baseEnd_7506657] using wordTrace_append hprefix tailTrace_7506657
  have hstable : (prefixWord ++ tailWord_7506657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506657).length < 2 ^ (prefixWord ++ tailWord_7506657).sum := by decide
  have hdescent : baseEnd_7506657 < baseStart_7506657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506700 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 2, 5, 2]
def baseStart_7506700 : Nat := 118140960795 + 7506700 * 2 ^ 59
def prefixEnd_7506700 : Nat := 4983230072969 + 3 ^ 40 * 7506700 * 2
def baseEnd_7506700 : Nat := 3854545229105885235427321

theorem tailTrace_7506700 : CollatzResearch.WordTrace tailWord_7506700 prefixEnd_7506700 3854545229105885235427321 := by
  unfold tailWord_7506700
  simp only [CollatzResearch.WordTrace]
  refine ⟨136895920952257708568254777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182527894603010278091006369 136895920952257708568254777)
  ·
    refine ⟨102671940714193281426191083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136895920952257708568254777 102671940714193281426191083)
    ·
      refine ⟨154007911071289922139286625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102671940714193281426191083 154007911071289922139286625)
      ·
        refine ⟨115505933303467441604464969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154007911071289922139286625 115505933303467441604464969)
        ·
          refine ⟨86629449977600581203348727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115505933303467441604464969 86629449977600581203348727)
          ·
            refine ⟨129944174966400871805023091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86629449977600581203348727 129944174966400871805023091)
            ·
              refine ⟨194916262449601307707534637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129944174966400871805023091 194916262449601307707534637)
              ·
                refine ⟨73093598418600490390325489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194916262449601307707534637 73093598418600490390325489)
                ·
                  refine ⟨54820198813950367792744117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73093598418600490390325489 54820198813950367792744117)
                  ·
                    refine ⟨5139393638807846980569761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54820198813950367792744117 5139393638807846980569761)
                    ·
                      refine ⟨3854545229105885235427321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139393638807846980569761 3854545229105885235427321)
                      ·
                        rfl

theorem cell23_7506700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_7506700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506700 prefixEnd_7506700 := by exact prefixLift 7506700
  have htrace : WordTrace (prefixWord ++ tailWord_7506700) baseStart_7506700 baseEnd_7506700 := by
    simpa [prefixWord, tailWord_7506700, baseEnd_7506700] using wordTrace_append hprefix tailTrace_7506700
  have hstable : (prefixWord ++ tailWord_7506700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506700).length < 2 ^ (prefixWord ++ tailWord_7506700).sum := by decide
  have hdescent : baseEnd_7506700 < baseStart_7506700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506703 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_7506703 : Nat := 118140960795 + 7506703 * 2 ^ 59
def prefixEnd_7506703 : Nat := 4983230072969 + 3 ^ 40 * 7506703 * 2
def baseEnd_7506703 : Nat := 3854546769547848723689807

theorem tailTrace_7506703 : CollatzResearch.WordTrace tailWord_7506703 prefixEnd_7506703 3854546769547848723689807 := by
  unfold tailWord_7506703
  simp only [CollatzResearch.WordTrace]
  refine ⟨273791951323504548648868763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182527967549003032432579175 273791951323504548648868763)
  ·
    refine ⟨410687926985256822973303145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273791951323504548648868763 410687926985256822973303145)
    ·
      refine ⟨308015945238942617229977359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410687926985256822973303145 308015945238942617229977359)
      ·
        refine ⟨462023917858413925844966039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308015945238942617229977359 462023917858413925844966039)
        ·
          refine ⟨693035876787620888767449059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462023917858413925844966039 693035876787620888767449059)
          ·
            refine ⟨1039553815181431333151173589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693035876787620888767449059 1039553815181431333151173589)
            ·
              refine ⟨24364542543314796870730631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1039553815181431333151173589 24364542543314796870730631)
              ·
                refine ⟨36546813814972195306095947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24364542543314796870730631 36546813814972195306095947)
                ·
                  refine ⟨54820220722458292959143921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36546813814972195306095947 54820220722458292959143921)
                  ·
                    refine ⟨41115165541843719719357941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54820220722458292959143921 41115165541843719719357941)
                    ·
                      refine ⟨3854546769547848723689807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41115165541843719719357941 3854546769547848723689807)
                      ·
                        rfl

theorem cell23_7506703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_7506703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506703 prefixEnd_7506703 := by exact prefixLift 7506703
  have htrace : WordTrace (prefixWord ++ tailWord_7506703) baseStart_7506703 baseEnd_7506703 := by
    simpa [prefixWord, tailWord_7506703, baseEnd_7506703] using wordTrace_append hprefix tailTrace_7506703
  have hstable : (prefixWord ++ tailWord_7506703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506703).length < 2 ^ (prefixWord ++ tailWord_7506703).sum := by decide
  have hdescent : baseEnd_7506703 < baseStart_7506703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506713 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_7506713 : Nat := 118140960795 + 7506713 * 2 ^ 59
def prefixEnd_7506713 : Nat := 4983230072969 + 3 ^ 40 * 7506713 * 2
def baseEnd_7506713 : Nat := 3854551904354393684564761

theorem tailTrace_7506713 : CollatzResearch.WordTrace tailWord_7506713 prefixEnd_7506713 3854551904354393684564761 := by
  unfold tailWord_7506713
  simp only [CollatzResearch.WordTrace]
  refine ⟨273792316053468320356732793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182528210702312213571155195 273792316053468320356732793)
  ·
    refine ⟨205344237040101240267549595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273792316053468320356732793 205344237040101240267549595)
    ·
      refine ⟨308016355560151860401324393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205344237040101240267549595 308016355560151860401324393)
      ·
        refine ⟨231012266670113895300993295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308016355560151860401324393 231012266670113895300993295)
        ·
          refine ⟨346518400005170842951489943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231012266670113895300993295 346518400005170842951489943)
          ·
            refine ⟨519777600007756264427234915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346518400005170842951489943 519777600007756264427234915)
            ·
              refine ⟨779666400011634396640852373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519777600007756264427234915 779666400011634396640852373)
              ·
                refine ⟨36546862500545362342539955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 779666400011634396640852373 36546862500545362342539955)
                ·
                  refine ⟨54820293750818043513809933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36546862500545362342539955 54820293750818043513809933)
                  ·
                    refine ⟨20557610156556766317678725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54820293750818043513809933 20557610156556766317678725)
                    ·
                      refine ⟨3854551904354393684564761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20557610156556766317678725 3854551904354393684564761)
                      ·
                        rfl

theorem cell23_7506713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_7506713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506713 prefixEnd_7506713 := by exact prefixLift 7506713
  have htrace : WordTrace (prefixWord ++ tailWord_7506713) baseStart_7506713 baseEnd_7506713 := by
    simpa [prefixWord, tailWord_7506713, baseEnd_7506713] using wordTrace_append hprefix tailTrace_7506713
  have hstable : (prefixWord ++ tailWord_7506713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506713).length < 2 ^ (prefixWord ++ tailWord_7506713).sum := by decide
  have hdescent : baseEnd_7506713 < baseStart_7506713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506743 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_7506743 : Nat := 118140960795 + 7506743 * 2 ^ 59
def prefixEnd_7506743 : Nat := 4983230072969 + 3 ^ 40 * 7506743 * 2
def baseEnd_7506743 : Nat := 3854567308774028567189623

theorem tailTrace_7506743 : CollatzResearch.WordTrace tailWord_7506743 prefixEnd_7506743 3854567308774028567189623 := by
  unfold tailWord_7506743
  simp only [CollatzResearch.WordTrace]
  refine ⟨273793410243359635480324883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182528940162239756986883255 273793410243359635480324883)
  ·
    refine ⟨410690115365039453220487325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273793410243359635480324883 410690115365039453220487325)
    ·
      refine ⟨154008793261889794957682747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410690115365039453220487325 154008793261889794957682747)
      ·
        refine ⟨231013189892834692436524121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154008793261889794957682747 231013189892834692436524121)
        ·
          refine ⟨173259892419626019327393091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231013189892834692436524121 173259892419626019327393091)
          ·
            refine ⟨259889838629439028991089637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173259892419626019327393091 259889838629439028991089637)
            ·
              refine ⟨48729344743019817935829307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259889838629439028991089637 48729344743019817935829307)
              ·
                refine ⟨73094017114529726903743961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48729344743019817935829307 73094017114529726903743961)
                ·
                  refine ⟨54820512835897295177807971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73094017114529726903743961 54820512835897295177807971)
                  ·
                    refine ⟨82230769253845942766711957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54820512835897295177807971 82230769253845942766711957)
                    ·
                      refine ⟨3854567308774028567189623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82230769253845942766711957 3854567308774028567189623)
                      ·
                        rfl

theorem cell23_7506743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_7506743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506743 prefixEnd_7506743 := by exact prefixLift 7506743
  have htrace : WordTrace (prefixWord ++ tailWord_7506743) baseStart_7506743 baseEnd_7506743 := by
    simpa [prefixWord, tailWord_7506743, baseEnd_7506743] using wordTrace_append hprefix tailTrace_7506743
  have hstable : (prefixWord ++ tailWord_7506743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506743).length < 2 ^ (prefixWord ++ tailWord_7506743).sum := by decide
  have hdescent : baseEnd_7506743 < baseStart_7506743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506770 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 6]
def baseStart_7506770 : Nat := 118140960795 + 7506770 * 2 ^ 59
def prefixEnd_7506770 : Nat := 4983230072969 + 3 ^ 40 * 7506770 * 2
def baseEnd_7506770 : Nat := 428286796972411106839111

theorem tailTrace_7506770 : CollatzResearch.WordTrace tailWord_7506770 prefixEnd_7506770 428286796972411106839111 := by
  unfold tailWord_7506770
  simp only [CollatzResearch.WordTrace]
  refine ⟨68448598753565454772889441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182529596676174546061038509 68448598753565454772889441)
  ·
    refine ⟨51336449065174091079667081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68448598753565454772889441 51336449065174091079667081)
    ·
      refine ⟨38502336798880568309750311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51336449065174091079667081 38502336798880568309750311)
      ·
        refine ⟨57753505198320852464625467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38502336798880568309750311 57753505198320852464625467)
        ·
          refine ⟨86630257797481278696938201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57753505198320852464625467 86630257797481278696938201)
          ·
            refine ⟨64972693348110959022703651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86630257797481278696938201 64972693348110959022703651)
            ·
              refine ⟨97459040022166438534055477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64972693348110959022703651 97459040022166438534055477)
              ·
                refine ⟨9136785002078103612567701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97459040022166438534055477 9136785002078103612567701)
                ·
                  refine ⟨428286796972411106839111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9136785002078103612567701 428286796972411106839111)
                  ·
                    rfl

theorem cell23_7506770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_7506770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506770 prefixEnd_7506770 := by exact prefixLift 7506770
  have htrace : WordTrace (prefixWord ++ tailWord_7506770) baseStart_7506770 baseEnd_7506770 := by
    simpa [prefixWord, tailWord_7506770, baseEnd_7506770] using wordTrace_append hprefix tailTrace_7506770
  have hstable : (prefixWord ++ tailWord_7506770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506770).length < 2 ^ (prefixWord ++ tailWord_7506770).sum := by decide
  have hdescent : baseEnd_7506770 < baseStart_7506770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506793 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_7506793 : Nat := 118140960795 + 7506793 * 2 ^ 59
def prefixEnd_7506793 : Nat := 4983230072969 + 3 ^ 40 * 7506793 * 2
def baseEnd_7506793 : Nat := 3854592982806753371564393

theorem tailTrace_7506793 : CollatzResearch.WordTrace tailWord_7506793 prefixEnd_7506793 3854592982806753371564393 := by
  unfold tailWord_7506793
  simp only [CollatzResearch.WordTrace]
  refine ⟨273795233893178494019645033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182530155928785662679763355 273795233893178494019645033)
  ·
    refine ⟨205346425419883870514733775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273795233893178494019645033 205346425419883870514733775)
    ·
      refine ⟨308019638129825805772100663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205346425419883870514733775 308019638129825805772100663)
      ·
        refine ⟨462029457194738708658150995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308019638129825805772100663 462029457194738708658150995)
        ·
          refine ⟨693044185792108062987226493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462029457194738708658150995 693044185792108062987226493)
          ·
            refine ⟨259891569672040523620209935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 693044185792108062987226493 259891569672040523620209935)
            ·
              refine ⟨389837354508060785430314903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259891569672040523620209935 389837354508060785430314903)
              ·
                refine ⟨584756031762091178145472355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389837354508060785430314903 584756031762091178145472355)
                ·
                  refine ⟨877134047643136767218208533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584756031762091178145472355 877134047643136767218208533)
                  ·
                    refine ⟨41115658483272035963353525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 877134047643136767218208533 41115658483272035963353525)
                    ·
                      refine ⟨3854592982806753371564393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41115658483272035963353525 3854592982806753371564393)
                      ·
                        rfl

theorem cell23_7506793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_7506793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506793 prefixEnd_7506793 := by exact prefixLift 7506793
  have htrace : WordTrace (prefixWord ++ tailWord_7506793) baseStart_7506793 baseEnd_7506793 := by
    simpa [prefixWord, tailWord_7506793, baseEnd_7506793] using wordTrace_append hprefix tailTrace_7506793
  have hstable : (prefixWord ++ tailWord_7506793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506793).length < 2 ^ (prefixWord ++ tailWord_7506793).sum := by decide
  have hdescent : baseEnd_7506793 < baseStart_7506793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506797 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_7506797 : Nat := 118140960795 + 7506797 * 2 ^ 59
def prefixEnd_7506797 : Nat := 4983230072969 + 3 ^ 40 * 7506797 * 2
def baseEnd_7506797 : Nat := 3854595036729371355914375

theorem tailTrace_7506797 : CollatzResearch.WordTrace tailWord_7506797 prefixEnd_7506797 3854595036729371355914375 := by
  unfold tailWord_7506797
  simp only [CollatzResearch.WordTrace]
  refine ⟨273795379785164002702790645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182530253190109335135193763 273795379785164002702790645)
  ·
    refine ⟨25668316854859125253386623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273795379785164002702790645 25668316854859125253386623)
    ·
      refine ⟨38502475282288687880079935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25668316854859125253386623 38502475282288687880079935)
      ·
        refine ⟨57753712923433031820119903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38502475282288687880079935 57753712923433031820119903)
        ·
          refine ⟨86630569385149547730179855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57753712923433031820119903 86630569385149547730179855)
          ·
            refine ⟨129945854077724321595269783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86630569385149547730179855 129945854077724321595269783)
            ·
              refine ⟨194918781116586482392904675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129945854077724321595269783 194918781116586482392904675)
              ·
                refine ⟨292378171674879723589357013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194918781116586482392904675 292378171674879723589357013)
                ·
                  refine ⟨6852613398629993521625555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 292378171674879723589357013 6852613398629993521625555)
                  ·
                    refine ⟨10278920097944990282438333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6852613398629993521625555 10278920097944990282438333)
                    ·
                      refine ⟨3854595036729371355914375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10278920097944990282438333 3854595036729371355914375)
                      ·
                        rfl

theorem cell23_7506797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_7506797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506797 prefixEnd_7506797 := by exact prefixLift 7506797
  have htrace : WordTrace (prefixWord ++ tailWord_7506797) baseStart_7506797 baseEnd_7506797 := by
    simpa [prefixWord, tailWord_7506797, baseEnd_7506797] using wordTrace_append hprefix tailTrace_7506797
  have hstable : (prefixWord ++ tailWord_7506797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506797).length < 2 ^ (prefixWord ++ tailWord_7506797).sum := by decide
  have hdescent : baseEnd_7506797 < baseStart_7506797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506807 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 2, 3, 2]
def baseStart_7506807 : Nat := 118140960795 + 7506807 * 2 ^ 59
def prefixEnd_7506807 : Nat := 4983230072969 + 3 ^ 40 * 7506807 * 2
def baseEnd_7506807 : Nat := 3854600171535916316789329

theorem tailTrace_7506807 : CollatzResearch.WordTrace tailWord_7506807 prefixEnd_7506807 3854600171535916316789329 := by
  unfold tailWord_7506807
  simp only [CollatzResearch.WordTrace]
  refine ⟨273795744515127774410654675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182530496343418516273769783 273795744515127774410654675)
  ·
    refine ⟨410693616772691661615982013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273795744515127774410654675 410693616772691661615982013)
    ·
      refine ⟨154010106289759373105993255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410693616772691661615982013 154010106289759373105993255)
      ·
        refine ⟨231015159434639059658989883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154010106289759373105993255 231015159434639059658989883)
        ·
          refine ⟨346522739151958589488484825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231015159434639059658989883 346522739151958589488484825)
          ·
            refine ⟨259892054363968942116363619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346522739151958589488484825 259892054363968942116363619)
            ·
              refine ⟨389838081545953413174545429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259892054363968942116363619 389838081545953413174545429)
              ·
                refine ⟨18273660072466566242556817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 389838081545953413174545429 18273660072466566242556817)
                ·
                  refine ⟨13705245054349924681917613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18273660072466566242556817 13705245054349924681917613)
                  ·
                    refine ⟨5139466895381221755719105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13705245054349924681917613 5139466895381221755719105)
                    ·
                      refine ⟨3854600171535916316789329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139466895381221755719105 3854600171535916316789329)
                      ·
                        rfl

theorem cell23_7506807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_7506807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506807 prefixEnd_7506807 := by exact prefixLift 7506807
  have htrace : WordTrace (prefixWord ++ tailWord_7506807) baseStart_7506807 baseEnd_7506807 := by
    simpa [prefixWord, tailWord_7506807, baseEnd_7506807] using wordTrace_append hprefix tailTrace_7506807
  have hstable : (prefixWord ++ tailWord_7506807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506807).length < 2 ^ (prefixWord ++ tailWord_7506807).sum := by decide
  have hdescent : baseEnd_7506807 < baseStart_7506807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506837 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 4]
def baseStart_7506837 : Nat := 118140960795 + 7506837 * 2 ^ 59
def prefixEnd_7506837 : Nat := 4983230072969 + 3 ^ 40 * 7506837 * 2
def baseEnd_7506837 : Nat := 3854615575955551199414191

theorem tailTrace_7506837 : CollatzResearch.WordTrace tailWord_7506837 prefixEnd_7506837 3854615575955551199414191 := by
  unfold tailWord_7506837
  simp only [CollatzResearch.WordTrace]
  refine ⟨273796838705019089534246765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182531225803346059689497843 273796838705019089534246765)
  ·
    refine ⟨102673814514382158575342537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273796838705019089534246765 102673814514382158575342537)
    ·
      refine ⟨77005360885786618931506903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102673814514382158575342537 77005360885786618931506903)
      ·
        refine ⟨115508041328679928397260355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77005360885786618931506903 115508041328679928397260355)
        ·
          refine ⟨173262061993019892595890533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115508041328679928397260355 173262061993019892595890533)
          ·
            refine ⟨32486636623691229861729475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173262061993019892595890533 32486636623691229861729475)
            ·
              refine ⟨48729954935536844792594213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32486636623691229861729475 48729954935536844792594213)
              ·
                refine ⟨9136866550413158398611415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48729954935536844792594213 9136866550413158398611415)
                ·
                  refine ⟨13705299825619737597917123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9136866550413158398611415 13705299825619737597917123)
                  ·
                    refine ⟨20557949738429606396875685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13705299825619737597917123 20557949738429606396875685)
                    ·
                      refine ⟨3854615575955551199414191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20557949738429606396875685 3854615575955551199414191)
                      ·
                        rfl

theorem cell23_7506837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_7506837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506837 prefixEnd_7506837 := by exact prefixLift 7506837
  have htrace : WordTrace (prefixWord ++ tailWord_7506837) baseStart_7506837 baseEnd_7506837 := by
    simpa [prefixWord, tailWord_7506837, baseEnd_7506837] using wordTrace_append hprefix tailTrace_7506837
  have hstable : (prefixWord ++ tailWord_7506837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506837).length < 2 ^ (prefixWord ++ tailWord_7506837).sum := by decide
  have hdescent : baseEnd_7506837 < baseStart_7506837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506847 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 4, 4]
def baseStart_7506847 : Nat := 118140960795 + 7506847 * 2 ^ 59
def prefixEnd_7506847 : Nat := 4983230072969 + 3 ^ 40 * 7506847 * 2
def baseEnd_7506847 : Nat := 1284873570254032053429715

theorem tailTrace_7506847 : CollatzResearch.WordTrace tailWord_7506847 prefixEnd_7506847 1284873570254032053429715 := by
  unfold tailWord_7506847
  simp only [CollatzResearch.WordTrace]
  refine ⟨273797203434982861242110795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182531468956655240828073863 273797203434982861242110795)
  ·
    refine ⟨410695805152474291863166193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273797203434982861242110795 410695805152474291863166193)
    ·
      refine ⟨308021853864355718897374645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410695805152474291863166193 308021853864355718897374645)
      ·
        refine ⟨28877048799783348646628873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308021853864355718897374645 28877048799783348646628873)
        ·
          refine ⟨21657786599837511484971655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28877048799783348646628873 21657786599837511484971655)
          ·
            refine ⟨32486679899756267227457483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21657786599837511484971655 32486679899756267227457483)
            ·
              refine ⟨48730019849634400841186225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32486679899756267227457483 48730019849634400841186225)
              ·
                refine ⟨36547514887225800630889669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48730019849634400841186225 36547514887225800630889669)
                ·
                  refine ⟨6852659041354837618291813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36547514887225800630889669 6852659041354837618291813)
                  ·
                    refine ⟨1284873570254032053429715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6852659041354837618291813 1284873570254032053429715)
                    ·
                      rfl

theorem cell23_7506847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 4].length) (baseStart_7506847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506847 prefixEnd_7506847 := by exact prefixLift 7506847
  have htrace : WordTrace (prefixWord ++ tailWord_7506847) baseStart_7506847 baseEnd_7506847 := by
    simpa [prefixWord, tailWord_7506847, baseEnd_7506847] using wordTrace_append hprefix tailTrace_7506847
  have hstable : (prefixWord ++ tailWord_7506847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506847).length < 2 ^ (prefixWord ++ tailWord_7506847).sum := by decide
  have hdescent : baseEnd_7506847 < baseStart_7506847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506857 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 3]
def baseStart_7506857 : Nat := 118140960795 + 7506857 * 2 ^ 59
def prefixEnd_7506857 : Nat := 4983230072969 + 3 ^ 40 * 7506857 * 2
def baseEnd_7506857 : Nat := 3854625845568641121164099

theorem tailTrace_7506857 : CollatzResearch.WordTrace tailWord_7506857 prefixEnd_7506857 3854625845568641121164099 := by
  unfold tailWord_7506857
  simp only [CollatzResearch.WordTrace]
  refine ⟨273797568164946632949974825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182531712109964421966649883 273797568164946632949974825)
  ·
    refine ⟨205348176123709974712481119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273797568164946632949974825 205348176123709974712481119)
    ·
      refine ⟨308022264185564962068721679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205348176123709974712481119 308022264185564962068721679)
      ·
        refine ⟨462033396278347443103082519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308022264185564962068721679 462033396278347443103082519)
        ·
          refine ⟨693050094417521164654623779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462033396278347443103082519 693050094417521164654623779)
          ·
            refine ⟨1039575141626281746981935669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693050094417521164654623779 1039575141626281746981935669)
            ·
              refine ⟨97460169527463913779556469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1039575141626281746981935669 97460169527463913779556469)
              ·
                refine ⟨9136890893199741916833419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97460169527463913779556469 9136890893199741916833419)
                ·
                  refine ⟨13705336339799612875250129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9136890893199741916833419 13705336339799612875250129)
                  ·
                    refine ⟨10279002254849709656437597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13705336339799612875250129 10279002254849709656437597)
                    ·
                      refine ⟨3854625845568641121164099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10279002254849709656437597 3854625845568641121164099)
                      ·
                        rfl

theorem cell23_7506857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 2, 3].length) (baseStart_7506857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506857 prefixEnd_7506857 := by exact prefixLift 7506857
  have htrace : WordTrace (prefixWord ++ tailWord_7506857) baseStart_7506857 baseEnd_7506857 := by
    simpa [prefixWord, tailWord_7506857, baseEnd_7506857] using wordTrace_append hprefix tailTrace_7506857
  have hstable : (prefixWord ++ tailWord_7506857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506857).length < 2 ^ (prefixWord ++ tailWord_7506857).sum := by decide
  have hdescent : baseEnd_7506857 < baseStart_7506857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506871 : List Nat := [1, 1, 3, 1, 3, 1, 2, 6, 1, 2, 2]
def baseStart_7506871 : Nat := 118140960795 + 7506871 * 2 ^ 59
def prefixEnd_7506871 : Nat := 4983230072969 + 3 ^ 40 * 7506871 * 2
def baseEnd_7506871 : Nat := 3854633034297804066389035

theorem tailTrace_7506871 : CollatzResearch.WordTrace tailWord_7506871 prefixEnd_7506871 3854633034297804066389035 := by
  unfold tailWord_7506871
  simp only [CollatzResearch.WordTrace]
  refine ⟨273798078786895913340984467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182532052524597275560656311 273798078786895913340984467)
  ·
    refine ⟨410697118180343870011476701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273798078786895913340984467 410697118180343870011476701)
    ·
      refine ⟨154011419317628951254303763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410697118180343870011476701 154011419317628951254303763)
      ·
        refine ⟨231017128976443426881455645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154011419317628951254303763 231017128976443426881455645)
        ·
          refine ⟨86631423366166285080545867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231017128976443426881455645 86631423366166285080545867)
          ·
            refine ⟨129947135049249427620818801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86631423366166285080545867 129947135049249427620818801)
            ·
              refine ⟨97460351286937070715614101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129947135049249427620818801 97460351286937070715614101)
              ·
                refine ⟨4568453966575175189794411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97460351286937070715614101 4568453966575175189794411)
                ·
                  refine ⟨6852680949862762784691617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568453966575175189794411 6852680949862762784691617)
                  ·
                    refine ⟨5139510712397072088518713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6852680949862762784691617 5139510712397072088518713)
                    ·
                      refine ⟨3854633034297804066389035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139510712397072088518713 3854633034297804066389035)
                      ·
                        rfl

theorem cell23_7506871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 2, 2].length) (baseStart_7506871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506871 prefixEnd_7506871 := by exact prefixLift 7506871
  have htrace : WordTrace (prefixWord ++ tailWord_7506871) baseStart_7506871 baseEnd_7506871 := by
    simpa [prefixWord, tailWord_7506871, baseEnd_7506871] using wordTrace_append hprefix tailTrace_7506871
  have hstable : (prefixWord ++ tailWord_7506871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506871).length < 2 ^ (prefixWord ++ tailWord_7506871).sum := by decide
  have hdescent : baseEnd_7506871 < baseStart_7506871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506877 : List Nat := [1, 4, 1, 2, 4, 1, 2, 8]
def baseStart_7506877 : Nat := 118140960795 + 7506877 * 2 ^ 59
def prefixEnd_7506877 : Nat := 4983230072969 + 3 ^ 40 * 7506877 * 2
def baseEnd_7506877 : Nat := 142764300562286334922741

theorem tailTrace_7506877 : CollatzResearch.WordTrace tailWord_7506877 prefixEnd_7506877 142764300562286334922741 := by
  unfold tailWord_7506877
  simp only [CollatzResearch.WordTrace]
  refine ⟨273798297624874176365702885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182532198416582784243801923 273798297624874176365702885)
  ·
    refine ⟨51337180804663908068569291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273798297624874176365702885 51337180804663908068569291)
    ·
      refine ⟨77005771206995862102853937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51337180804663908068569291 77005771206995862102853937)
      ·
        refine ⟨57754328405246896577140453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77005771206995862102853937 57754328405246896577140453)
        ·
          refine ⟨10828936575983793108213835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57754328405246896577140453 10828936575983793108213835)
          ·
            refine ⟨16243404863975689662320753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10828936575983793108213835 16243404863975689662320753)
            ·
              refine ⟨12182553647981767246740565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16243404863975689662320753 12182553647981767246740565)
              ·
                refine ⟨142764300562286334922741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12182553647981767246740565 142764300562286334922741)
                ·
                  rfl

theorem cell23_7506877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 8].length) (baseStart_7506877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506877 prefixEnd_7506877 := by exact prefixLift 7506877
  have htrace : WordTrace (prefixWord ++ tailWord_7506877) baseStart_7506877 baseEnd_7506877 := by
    simpa [prefixWord, tailWord_7506877, baseEnd_7506877] using wordTrace_append hprefix tailTrace_7506877
  have hstable : (prefixWord ++ tailWord_7506877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506877).length < 2 ^ (prefixWord ++ tailWord_7506877).sum := by decide
  have hdescent : baseEnd_7506877 < baseStart_7506877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7506978 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 2, 2, 2]
def baseStart_7506978 : Nat := 118140960795 + 7506978 * 2 ^ 59
def prefixEnd_7506978 : Nat := 4983230072969 + 3 ^ 40 * 7506978 * 2
def baseEnd_7506978 : Nat := 3854687976727835147751043

theorem tailTrace_7506978 : CollatzResearch.WordTrace tailWord_7506978 prefixEnd_7506978 3854687976727835147751043 := by
  unfold tailWord_7506978
  simp only [CollatzResearch.WordTrace]
  refine ⟨68450495349377067653782397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182534654265005513743419725 68450495349377067653782397)
  ·
    refine ⟨25668935756016400370168399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68450495349377067653782397 25668935756016400370168399)
    ·
      refine ⟨38503403634024600555252599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25668935756016400370168399 38503403634024600555252599)
      ·
        refine ⟨57755105451036900832878899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38503403634024600555252599 57755105451036900832878899)
        ·
          refine ⟨86632658176555351249318349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57755105451036900832878899 86632658176555351249318349)
          ·
            refine ⟨32487246816208256718494381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86632658176555351249318349 32487246816208256718494381)
            ·
              refine ⟨12182717556078096269435393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32487246816208256718494381 12182717556078096269435393)
              ·
                refine ⟨9137038167058572202076545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12182717556078096269435393 9137038167058572202076545)
                ·
                  refine ⟨6852778625293929151557409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9137038167058572202076545 6852778625293929151557409)
                  ·
                    refine ⟨5139583968970446863668057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6852778625293929151557409 5139583968970446863668057)
                    ·
                      refine ⟨3854687976727835147751043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139583968970446863668057 3854687976727835147751043)
                      ·
                        rfl

theorem cell23_7506978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_7506978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7506978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7506978 prefixEnd_7506978 := by exact prefixLift 7506978
  have htrace : WordTrace (prefixWord ++ tailWord_7506978) baseStart_7506978 baseEnd_7506978 := by
    simpa [prefixWord, tailWord_7506978, baseEnd_7506978] using wordTrace_append hprefix tailTrace_7506978
  have hstable : (prefixWord ++ tailWord_7506978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7506978).length < 2 ^ (prefixWord ++ tailWord_7506978).sum := by decide
  have hdescent : baseEnd_7506978 < baseStart_7506978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7506978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507027 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 7, 4]
def baseStart_7507027 : Nat := 118140960795 + 7507027 * 2 ^ 59
def prefixEnd_7507027 : Nat := 4983230072969 + 3 ^ 40 * 7507027 * 2
def baseEnd_7507027 : Nat := 1284904379093301818679439

theorem tailTrace_7507027 : CollatzResearch.WordTrace tailWord_7507027 prefixEnd_7507027 1284904379093301818679439 := by
  unfold tailWord_7507027
  simp only [CollatzResearch.WordTrace]
  refine ⟨273803768574330751983663335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182535845716220501322442223 273803768574330751983663335)
  ·
    refine ⟨410705652861496127975495003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273803768574330751983663335 410705652861496127975495003)
    ·
      refine ⟨616058479292244191963242505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410705652861496127975495003 616058479292244191963242505)
      ·
        refine ⟨462043859469183143972431879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616058479292244191963242505 462043859469183143972431879)
        ·
          refine ⟨693065789203774715958647819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462043859469183143972431879 693065789203774715958647819)
          ·
            refine ⟨1039598683805662073937971729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693065789203774715958647819 1039598683805662073937971729)
            ·
              refine ⟨779699012854246555453478797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039598683805662073937971729 779699012854246555453478797)
              ·
                refine ⟨292387129820342458295054549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 779699012854246555453478797 292387129820342458295054549)
                ·
                  refine ⟨6852823355164276366290341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 292387129820342458295054549 6852823355164276366290341)
                  ·
                    refine ⟨1284904379093301818679439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6852823355164276366290341 1284904379093301818679439)
                    ·
                      rfl

theorem cell23_7507027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 4].length) (baseStart_7507027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507027 prefixEnd_7507027 := by exact prefixLift 7507027
  have htrace : WordTrace (prefixWord ++ tailWord_7507027) baseStart_7507027 baseEnd_7507027 := by
    simpa [prefixWord, tailWord_7507027, baseEnd_7507027] using wordTrace_append hprefix tailTrace_7507027
  have hstable : (prefixWord ++ tailWord_7507027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507027).length < 2 ^ (prefixWord ++ tailWord_7507027).sum := by decide
  have hdescent : baseEnd_7507027 < baseStart_7507027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507034 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2]
def baseStart_7507034 : Nat := 118140960795 + 7507034 * 2 ^ 59
def prefixEnd_7507034 : Nat := 4983230072969 + 3 ^ 40 * 7507034 * 2
def baseEnd_7507034 : Nat := 3854716731644486928650785

theorem tailTrace_7507034 : CollatzResearch.WordTrace tailWord_7507034 prefixEnd_7507034 3854716731644486928650785 := by
  unfold tailWord_7507034
  simp only [CollatzResearch.WordTrace]
  refine ⟨68451005971326348044792039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182536015923536928119445437 68451005971326348044792039)
  ·
    refine ⟨102676508956989522067188059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68451005971326348044792039 102676508956989522067188059)
    ·
      refine ⟨154014763435484283100782089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102676508956989522067188059 154014763435484283100782089)
      ·
        refine ⟨115511072576613212325586567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154014763435484283100782089 115511072576613212325586567)
        ·
          refine ⟨173266608864919818488379851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115511072576613212325586567 173266608864919818488379851)
          ·
            refine ⟨259899913297379727732569777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173266608864919818488379851 259899913297379727732569777)
            ·
              refine ⟨194924934973034795799427333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259899913297379727732569777 194924934973034795799427333)
              ·
                refine ⟨36548425307444024212392625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194924934973034795799427333 36548425307444024212392625)
                ·
                  refine ⟨27411318980583018159294469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36548425307444024212392625 27411318980583018159294469)
                  ·
                    refine ⟨5139622308859315904867713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27411318980583018159294469 5139622308859315904867713)
                    ·
                      refine ⟨3854716731644486928650785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139622308859315904867713 3854716731644486928650785)
                      ·
                        rfl

theorem cell23_7507034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_7507034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507034 prefixEnd_7507034 := by exact prefixLift 7507034
  have htrace : WordTrace (prefixWord ++ tailWord_7507034) baseStart_7507034 baseEnd_7507034 := by
    simpa [prefixWord, tailWord_7507034, baseEnd_7507034] using wordTrace_append hprefix tailTrace_7507034
  have hstable : (prefixWord ++ tailWord_7507034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507034).length < 2 ^ (prefixWord ++ tailWord_7507034).sum := by decide
  have hdescent : baseEnd_7507034 < baseStart_7507034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507067 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 3]
def baseStart_7507067 : Nat := 118140960795 + 7507067 * 2 ^ 59
def prefixEnd_7507067 : Nat := 4983230072969 + 3 ^ 40 * 7507067 * 2
def baseEnd_7507067 : Nat := 3854733676506085299538133

theorem tailTrace_7507067 : CollatzResearch.WordTrace tailWord_7507067 prefixEnd_7507067 3854733676506085299538133 := by
  unfold tailWord_7507067
  simp only [CollatzResearch.WordTrace]
  refine ⟨273805227494185838815119455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182536818329457225876746303 273805227494185838815119455)
  ·
    refine ⟨410707841241278758222679183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273805227494185838815119455 410707841241278758222679183)
    ·
      refine ⟨616061761861918137334018775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410707841241278758222679183 616061761861918137334018775)
      ·
        refine ⟨924092642792877206001028163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616061761861918137334018775 924092642792877206001028163)
        ·
          refine ⟨1386138964189315809001542245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924092642792877206001028163 1386138964189315809001542245)
          ·
            refine ⟨259901055785496714187789171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1386138964189315809001542245 259901055785496714187789171)
            ·
              refine ⟨389851583678245071281683757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259901055785496714187789171 389851583678245071281683757)
              ·
                refine ⟨146194343879341901730631409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389851583678245071281683757 146194343879341901730631409)
                ·
                  refine ⟨109645757909506426297973557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146194343879341901730631409 109645757909506426297973557)
                  ·
                    refine ⟨10279289804016227465435021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109645757909506426297973557 10279289804016227465435021)
                    ·
                      refine ⟨3854733676506085299538133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10279289804016227465435021 3854733676506085299538133)
                      ·
                        rfl

theorem cell23_7507067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 3].length) (baseStart_7507067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507067 prefixEnd_7507067 := by exact prefixLift 7507067
  have htrace : WordTrace (prefixWord ++ tailWord_7507067) baseStart_7507067 baseEnd_7507067 := by
    simpa [prefixWord, tailWord_7507067, baseEnd_7507067] using wordTrace_append hprefix tailTrace_7507067
  have hstable : (prefixWord ++ tailWord_7507067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507067).length < 2 ^ (prefixWord ++ tailWord_7507067).sum := by decide
  have hdescent : baseEnd_7507067 < baseStart_7507067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507095 : List Nat := [1, 1, 3, 3, 3, 3, 2, 2, 1, 4]
def baseStart_7507095 : Nat := 118140960795 + 7507095 * 2 ^ 59
def prefixEnd_7507095 : Nat := 4983230072969 + 3 ^ 40 * 7507095 * 2
def baseEnd_7507095 : Nat := 1284916017988137063329335

theorem tailTrace_7507095 : CollatzResearch.WordTrace tailWord_7507095 prefixEnd_7507095 1284916017988137063329335 := by
  unfold tailWord_7507095
  simp only [CollatzResearch.WordTrace]
  refine ⟨273806248738084399597138739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182537499158722933064759159 273806248738084399597138739)
  ·
    refine ⟨410709373107126599395708109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273806248738084399597138739 410709373107126599395708109)
    ·
      refine ⟨154016014915172474773390541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410709373107126599395708109 154016014915172474773390541)
      ·
        refine ⟨57756005593189678040021453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154016014915172474773390541 57756005593189678040021453)
        ·
          refine ⟨21658502097446129265008045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57756005593189678040021453 21658502097446129265008045)
          ·
            refine ⟨8121938286542298474378017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21658502097446129265008045 8121938286542298474378017)
            ·
              refine ⟨6091453714906723855783513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8121938286542298474378017 6091453714906723855783513)
              ·
                refine ⟨4568590286180042891837635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6091453714906723855783513 4568590286180042891837635)
                ·
                  refine ⟨6852885429270064337756453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568590286180042891837635 6852885429270064337756453)
                  ·
                    refine ⟨1284916017988137063329335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6852885429270064337756453 1284916017988137063329335)
                    ·
                      rfl

theorem cell23_7507095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_7507095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507095 prefixEnd_7507095 := by exact prefixLift 7507095
  have htrace : WordTrace (prefixWord ++ tailWord_7507095) baseStart_7507095 baseEnd_7507095 := by
    simpa [prefixWord, tailWord_7507095, baseEnd_7507095] using wordTrace_append hprefix tailTrace_7507095
  have hstable : (prefixWord ++ tailWord_7507095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507095).length < 2 ^ (prefixWord ++ tailWord_7507095).sum := by decide
  have hdescent : baseEnd_7507095 < baseStart_7507095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507101 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_7507101 : Nat := 118140960795 + 7507101 * 2 ^ 59
def prefixEnd_7507101 : Nat := 4983230072969 + 3 ^ 40 * 7507101 * 2
def baseEnd_7507101 : Nat := 3854751134848338166512977

theorem tailTrace_7507101 : CollatzResearch.WordTrace tailWord_7507101 prefixEnd_7507101 3854751134848338166512977 := by
  unfold tailWord_7507101
  simp only [CollatzResearch.WordTrace]
  refine ⟨273806467576062662621857157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182537645050708441747904771 273806467576062662621857157)
  ·
    refine ⟨51338712670511749241598217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273806467576062662621857157 51338712670511749241598217)
    ·
      refine ⟨38504034502883811931198663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51338712670511749241598217 38504034502883811931198663)
      ·
        refine ⟨57756051754325717896797995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38504034502883811931198663 57756051754325717896797995)
        ·
          refine ⟨86634077631488576845196993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57756051754325717896797995 86634077631488576845196993)
          ·
            refine ⟨64975558223616432633897745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86634077631488576845196993 64975558223616432633897745)
            ·
              refine ⟨48731668667712324475423309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64975558223616432633897745 48731668667712324475423309)
              ·
                refine ⟨18274375750392121678283741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48731668667712324475423309 18274375750392121678283741)
                ·
                  refine ⟨6852890906397045629356403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18274375750392121678283741 6852890906397045629356403)
                  ·
                    refine ⟨10279336359595568444034605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6852890906397045629356403 10279336359595568444034605)
                    ·
                      refine ⟨3854751134848338166512977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10279336359595568444034605 3854751134848338166512977)
                      ·
                        rfl

theorem cell23_7507101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_7507101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507101 prefixEnd_7507101 := by exact prefixLift 7507101
  have htrace : WordTrace (prefixWord ++ tailWord_7507101) baseStart_7507101 baseEnd_7507101 := by
    simpa [prefixWord, tailWord_7507101, baseEnd_7507101] using wordTrace_append hprefix tailTrace_7507101
  have hstable : (prefixWord ++ tailWord_7507101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507101).length < 2 ^ (prefixWord ++ tailWord_7507101).sum := by decide
  have hdescent : baseEnd_7507101 < baseStart_7507101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507141 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 7, 2, 2]
def baseStart_7507141 : Nat := 118140960795 + 7507141 * 2 ^ 59
def prefixEnd_7507141 : Nat := 4983230072969 + 3 ^ 40 * 7507141 * 2
def baseEnd_7507141 : Nat := 3854771674074518010012793

theorem tailTrace_7507141 : CollatzResearch.WordTrace tailWord_7507141 prefixEnd_7507141 3854771674074518010012793 := by
  unfold tailWord_7507141
  simp only [CollatzResearch.WordTrace]
  refine ⟨273807926495917749453313277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182538617663945166302208851 273807926495917749453313277)
  ·
    refine ⟨102677972435969156044992479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273807926495917749453313277 102677972435969156044992479)
    ·
      refine ⟨154016958653953734067488719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102677972435969156044992479 154016958653953734067488719)
      ·
        refine ⟨231025437980930601101233079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154016958653953734067488719 231025437980930601101233079)
        ·
          refine ⟨346538156971395901651849619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231025437980930601101233079 346538156971395901651849619)
          ·
            refine ⟨519807235457093852477774429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346538156971395901651849619 519807235457093852477774429)
            ·
              refine ⟨194927713296410194679165411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519807235457093852477774429 194927713296410194679165411)
              ·
                refine ⟨292391569944615292018748117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194927713296410194679165411 292391569944615292018748117)
                ·
                  refine ⟨6852927420576920906689409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 292391569944615292018748117 6852927420576920906689409)
                  ·
                    refine ⟨5139695565432690680017057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6852927420576920906689409 5139695565432690680017057)
                    ·
                      refine ⟨3854771674074518010012793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139695565432690680017057 3854771674074518010012793)
                      ·
                        rfl

theorem cell23_7507141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_7507141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507141 prefixEnd_7507141 := by exact prefixLift 7507141
  have htrace : WordTrace (prefixWord ++ tailWord_7507141) baseStart_7507141 baseEnd_7507141 := by
    simpa [prefixWord, tailWord_7507141, baseEnd_7507141] using wordTrace_append hprefix tailTrace_7507141
  have hstable : (prefixWord ++ tailWord_7507141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507141).length < 2 ^ (prefixWord ++ tailWord_7507141).sum := by decide
  have hdescent : baseEnd_7507141 < baseStart_7507141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507142 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_7507142 : Nat := 118140960795 + 7507142 * 2 ^ 59
def prefixEnd_7507142 : Nat := 4983230072969 + 3 ^ 40 * 7507142 * 2
def baseEnd_7507142 : Nat := 428308020839463611788921

theorem tailTrace_7507142 : CollatzResearch.WordTrace tailWord_7507142 prefixEnd_7507142 428308020839463611788921 := by
  unfold tailWord_7507142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8556498842778566457003115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182538641979276084416066453 8556498842778566457003115)
  ·
    refine ⟨12834748264167849685504673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8556498842778566457003115 12834748264167849685504673)
    ·
      refine ⟨9626061198125887264128505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12834748264167849685504673 9626061198125887264128505)
      ·
        refine ⟨7219545898594415448096379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9626061198125887264128505 7219545898594415448096379)
        ·
          refine ⟨10829318847891623172144569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7219545898594415448096379 10829318847891623172144569)
          ·
            refine ⟨8121989135918717379108427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10829318847891623172144569 8121989135918717379108427)
            ·
              refine ⟨12182983703878076068662641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8121989135918717379108427 12182983703878076068662641)
              ·
                refine ⟨9137237777908557051496981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12182983703878076068662641 9137237777908557051496981)
                ·
                  refine ⟨428308020839463611788921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9137237777908557051496981 428308020839463611788921)
                  ·
                    rfl

theorem cell23_7507142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_7507142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507142 prefixEnd_7507142 := by exact prefixLift 7507142
  have htrace : WordTrace (prefixWord ++ tailWord_7507142) baseStart_7507142 baseEnd_7507142 := by
    simpa [prefixWord, tailWord_7507142, baseEnd_7507142] using wordTrace_append hprefix tailTrace_7507142
  have hstable : (prefixWord ++ tailWord_7507142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507142).length < 2 ^ (prefixWord ++ tailWord_7507142).sum := by decide
  have hdescent : baseEnd_7507142 < baseStart_7507142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507154 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_7507154 : Nat := 118140960795 + 7507154 * 2 ^ 59
def prefixEnd_7507154 : Nat := 4983230072969 + 3 ^ 40 * 7507154 * 2
def baseEnd_7507154 : Nat := 3854778349323026459150233

theorem tailTrace_7507154 : CollatzResearch.WordTrace tailWord_7507154 prefixEnd_7507154 3854778349323026459150233 := by
  unfold tailWord_7507154
  simp only [CollatzResearch.WordTrace]
  refine ⟨68452100161217663168384129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182538933763247101782357677 68452100161217663168384129)
  ·
    refine ⟨51339075120913247376288097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68452100161217663168384129 51339075120913247376288097)
    ·
      refine ⟨38504306340684935532216073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51339075120913247376288097 38504306340684935532216073)
      ·
        refine ⟨28878229755513701649162055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38504306340684935532216073 28878229755513701649162055)
        ·
          refine ⟨43317344633270552473743083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28878229755513701649162055 43317344633270552473743083)
          ·
            refine ⟨64976016949905828710614625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43317344633270552473743083 64976016949905828710614625)
            ·
              refine ⟨48732012712429371532960969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64976016949905828710614625 48732012712429371532960969)
              ·
                refine ⟨36549009534322028649720727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48732012712429371532960969 36549009534322028649720727)
                ·
                  refine ⟨54823514301483042974581091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36549009534322028649720727 54823514301483042974581091)
                  ·
                    refine ⟨82235271452224564461871637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54823514301483042974581091 82235271452224564461871637)
                    ·
                      refine ⟨3854778349323026459150233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82235271452224564461871637 3854778349323026459150233)
                      ·
                        rfl

theorem cell23_7507154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_7507154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507154 prefixEnd_7507154 := by exact prefixLift 7507154
  have htrace : WordTrace (prefixWord ++ tailWord_7507154) baseStart_7507154 baseEnd_7507154 := by
    simpa [prefixWord, tailWord_7507154, baseEnd_7507154] using wordTrace_append hprefix tailTrace_7507154
  have hstable : (prefixWord ++ tailWord_7507154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507154).length < 2 ^ (prefixWord ++ tailWord_7507154).sum := by decide
  have hdescent : baseEnd_7507154 < baseStart_7507154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507168 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 2, 4]
def baseStart_7507168 : Nat := 118140960795 + 7507168 * 2 ^ 59
def prefixEnd_7507168 : Nat := 4983230072969 + 3 ^ 40 * 7507168 * 2
def baseEnd_7507168 : Nat := 1284928512684063134791723

theorem tailTrace_7507168 : CollatzResearch.WordTrace tailWord_7507168 prefixEnd_7507168 1284928512684063134791723 := by
  unfold tailWord_7507168
  simp only [CollatzResearch.WordTrace]
  refine ⟨136904455633409966532273079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182539274177879955376364105 136904455633409966532273079)
  ·
    refine ⟨205356683450114949798409619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136904455633409966532273079 205356683450114949798409619)
    ·
      refine ⟨308035025175172424697614429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205356683450114949798409619 308035025175172424697614429)
      ·
        refine ⟨115513134440689659261605411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308035025175172424697614429 115513134440689659261605411)
        ·
          refine ⟨173269701661034488892408117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115513134440689659261605411 173269701661034488892408117)
          ·
            refine ⟨16244034530721983333663261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173269701661034488892408117 16244034530721983333663261)
            ·
              refine ⟨6091512949020743750123723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16244034530721983333663261 6091512949020743750123723)
              ·
                refine ⟨9137269423531115625185585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091512949020743750123723 9137269423531115625185585)
                ·
                  refine ⟨6852952067648336718889189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9137269423531115625185585 6852952067648336718889189)
                  ·
                    refine ⟨1284928512684063134791723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6852952067648336718889189 1284928512684063134791723)
                    ·
                      rfl

theorem cell23_7507168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 2, 4].length) (baseStart_7507168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507168 prefixEnd_7507168 := by exact prefixLift 7507168
  have htrace : WordTrace (prefixWord ++ tailWord_7507168) baseStart_7507168 baseEnd_7507168 := by
    simpa [prefixWord, tailWord_7507168, baseEnd_7507168] using wordTrace_append hprefix tailTrace_7507168
  have hstable : (prefixWord ++ tailWord_7507168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507168).length < 2 ^ (prefixWord ++ tailWord_7507168).sum := by decide
  have hdescent : baseEnd_7507168 < baseStart_7507168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507178 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_7507178 : Nat := 118140960795 + 7507178 * 2 ^ 59
def prefixEnd_7507178 : Nat := 4983230072969 + 3 ^ 40 * 7507178 * 2
def baseEnd_7507178 : Nat := 3854790672858734365250123

theorem tailTrace_7507178 : CollatzResearch.WordTrace tailWord_7507178 prefixEnd_7507178 3854790672858734365250123 := by
  unfold tailWord_7507178
  simp only [CollatzResearch.WordTrace]
  refine ⟨68452318999195926193102547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182539517331189136514940125 68452318999195926193102547)
  ·
    refine ⟨102678478498793889289653821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68452318999195926193102547 102678478498793889289653821)
    ·
      refine ⟨38504429437047708483620183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102678478498793889289653821 38504429437047708483620183)
      ·
        refine ⟨57756644155571562725430275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38504429437047708483620183 57756644155571562725430275)
        ·
          refine ⟨86634966233357344088145413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57756644155571562725430275 86634966233357344088145413)
          ·
            refine ⟨16244056168754502016527265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86634966233357344088145413 16244056168754502016527265)
            ·
              refine ⟨12183042126565876512395449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16244056168754502016527265 12183042126565876512395449)
              ·
                refine ⟨9137281594924407384296587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12183042126565876512395449 9137281594924407384296587)
                ·
                  refine ⟨13705922392386611076444881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137281594924407384296587 13705922392386611076444881)
                  ·
                    refine ⟨10279441794289958307333661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13705922392386611076444881 10279441794289958307333661)
                    ·
                      refine ⟨3854790672858734365250123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10279441794289958307333661 3854790672858734365250123)
                      ·
                        rfl

theorem cell23_7507178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_7507178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507178 prefixEnd_7507178 := by exact prefixLift 7507178
  have htrace : WordTrace (prefixWord ++ tailWord_7507178) baseStart_7507178 baseEnd_7507178 := by
    simpa [prefixWord, tailWord_7507178, baseEnd_7507178] using wordTrace_append hprefix tailTrace_7507178
  have hstable : (prefixWord ++ tailWord_7507178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507178).length < 2 ^ (prefixWord ++ tailWord_7507178).sum := by decide
  have hdescent : baseEnd_7507178 < baseStart_7507178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507181 : List Nat := [1, 5, 1, 2, 2, 1, 4, 7]
def baseStart_7507181 : Nat := 118140960795 + 7507181 * 2 ^ 59
def prefixEnd_7507181 : Nat := 4983230072969 + 3 ^ 40 * 7507181 * 2
def baseEnd_7507181 : Nat := 142770081974099920500467

theorem tailTrace_7507181 : CollatzResearch.WordTrace tailWord_7507181 prefixEnd_7507181 142770081974099920500467 := by
  unfold tailWord_7507181
  simp only [CollatzResearch.WordTrace]
  refine ⟨273809385415772836284769397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182539590277181890856512931 273809385415772836284769397)
  ·
    refine ⟨25669629882728703401697131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273809385415772836284769397 25669629882728703401697131)
    ·
      refine ⟨38504444824093055102545697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25669629882728703401697131 38504444824093055102545697)
      ·
        refine ⟨28878333618069791326909273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38504444824093055102545697 28878333618069791326909273)
        ·
          refine ⟨21658750213552343495181955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28878333618069791326909273 21658750213552343495181955)
          ·
            refine ⟨32488125320328515242772933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21658750213552343495181955 32488125320328515242772933)
            ·
              refine ⟨6091523497561596608019925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32488125320328515242772933 6091523497561596608019925)
              ·
                refine ⟨142770081974099920500467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6091523497561596608019925 142770081974099920500467)
                ·
                  rfl

theorem cell23_7507181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 7].length) (baseStart_7507181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507181 prefixEnd_7507181 := by exact prefixLift 7507181
  have htrace : WordTrace (prefixWord ++ tailWord_7507181) baseStart_7507181 baseEnd_7507181 := by
    simpa [prefixWord, tailWord_7507181, baseEnd_7507181] using wordTrace_append hprefix tailTrace_7507181
  have hstable : (prefixWord ++ tailWord_7507181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507181).length < 2 ^ (prefixWord ++ tailWord_7507181).sum := by decide
  have hdescent : baseEnd_7507181 < baseStart_7507181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507235 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 1, 3, 2]
def baseStart_7507235 : Nat := 118140960795 + 7507235 * 2 ^ 59
def prefixEnd_7507235 : Nat := 4983230072969 + 3 ^ 40 * 7507235 * 2
def baseEnd_7507235 : Nat := 3854819941256040642237361

theorem tailTrace_7507235 : CollatzResearch.WordTrace tailWord_7507235 prefixEnd_7507235 3854819941256040642237361 := by
  unfold tailWord_7507235
  simp only [CollatzResearch.WordTrace]
  refine ⟨273811354957577203507235159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182540903305051469004823439 273811354957577203507235159)
  ·
    refine ⟨410717032436365805260852739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273811354957577203507235159 410717032436365805260852739)
    ·
      refine ⟨616075548654548707891279109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410717032436365805260852739 616075548654548707891279109)
      ·
        refine ⟨115514165372727882729614833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 616075548654548707891279109 115514165372727882729614833)
        ·
          refine ⟨86635624029545912047211125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115514165372727882729614833 86635624029545912047211125)
          ·
            refine ⟨8122089752769929254426043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86635624029545912047211125 8122089752769929254426043)
            ·
              refine ⟨12183134629154893881639065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122089752769929254426043 12183134629154893881639065)
              ·
                refine ⟨9137350971866170411229299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12183134629154893881639065 9137350971866170411229299)
                ·
                  refine ⟨13706026457799255616843949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137350971866170411229299 13706026457799255616843949)
                  ·
                    refine ⟨5139759921674720856316481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13706026457799255616843949 5139759921674720856316481)
                    ·
                      refine ⟨3854819941256040642237361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139759921674720856316481 3854819941256040642237361)
                      ·
                        rfl

theorem cell23_7507235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_7507235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507235 prefixEnd_7507235 := by exact prefixLift 7507235
  have htrace : WordTrace (prefixWord ++ tailWord_7507235) baseStart_7507235 baseEnd_7507235 := by
    simpa [prefixWord, tailWord_7507235, baseEnd_7507235] using wordTrace_append hprefix tailTrace_7507235
  have hstable : (prefixWord ++ tailWord_7507235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507235).length < 2 ^ (prefixWord ++ tailWord_7507235).sum := by decide
  have hdescent : baseEnd_7507235 < baseStart_7507235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507244 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_7507244 : Nat := 118140960795 + 7507244 * 2 ^ 59
def prefixEnd_7507244 : Nat := 4983230072969 + 3 ^ 40 * 7507244 * 2
def baseEnd_7507244 : Nat := 3854824562581931107024819

theorem tailTrace_7507244 : CollatzResearch.WordTrace tailWord_7507244 prefixEnd_7507244 3854824562581931107024819 := by
  unfold tailWord_7507244
  simp only [CollatzResearch.WordTrace]
  refine ⟨136905841607272299022156393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182541122143029732029541857 136905841607272299022156393)
  ·
    refine ⟨102679381205454224266617295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136905841607272299022156393 102679381205454224266617295)
    ·
      refine ⟨154019071808181336399925943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102679381205454224266617295 154019071808181336399925943)
      ·
        refine ⟨231028607712272004599888915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154019071808181336399925943 231028607712272004599888915)
        ·
          refine ⟨346542911568408006899833373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231028607712272004599888915 346542911568408006899833373)
          ·
            refine ⟨129953591838153002587437515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346542911568408006899833373 129953591838153002587437515)
            ·
              refine ⟨194930387757229503881156273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129953591838153002587437515 194930387757229503881156273)
              ·
                refine ⟨146197790817922127910867205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194930387757229503881156273 146197790817922127910867205)
                ·
                  refine ⟨27412085778360398983287601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146197790817922127910867205 27412085778360398983287601)
                  ·
                    refine ⟨20559064333770299237465701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27412085778360398983287601 20559064333770299237465701)
                    ·
                      refine ⟨3854824562581931107024819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20559064333770299237465701 3854824562581931107024819)
                      ·
                        rfl

theorem cell23_7507244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_7507244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507244 prefixEnd_7507244 := by exact prefixLift 7507244
  have htrace : WordTrace (prefixWord ++ tailWord_7507244) baseStart_7507244 baseEnd_7507244 := by
    simpa [prefixWord, tailWord_7507244, baseEnd_7507244] using wordTrace_append hprefix tailTrace_7507244
  have hstable : (prefixWord ++ tailWord_7507244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507244).length < 2 ^ (prefixWord ++ tailWord_7507244).sum := by decide
  have hdescent : baseEnd_7507244 < baseStart_7507244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507252 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_7507252 : Nat := 118140960795 + 7507252 * 2 ^ 59
def prefixEnd_7507252 : Nat := 4983230072969 + 3 ^ 40 * 7507252 * 2
def baseEnd_7507252 : Nat := 3854828670427167075724783

theorem tailTrace_7507252 : CollatzResearch.WordTrace tailWord_7507252 prefixEnd_7507252 3854828670427167075724783 := by
  unfold tailWord_7507252
  simp only [CollatzResearch.WordTrace]
  refine ⟨136905987499257807705302005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182541316665677076940402673 136905987499257807705302005)
  ·
    refine ⟨12834936328055419472372063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136905987499257807705302005 12834936328055419472372063)
    ·
      refine ⟨19252404492083129208558095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12834936328055419472372063 19252404492083129208558095)
      ·
        refine ⟨28878606738124693812837143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19252404492083129208558095 28878606738124693812837143)
        ·
          refine ⟨43317910107187040719255715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28878606738124693812837143 43317910107187040719255715)
          ·
            refine ⟨64976865160780561078883573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43317910107187040719255715 64976865160780561078883573)
            ·
              refine ⟨6091581108823177601145335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64976865160780561078883573 6091581108823177601145335)
              ·
                refine ⟨9137371663234766401718003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091581108823177601145335 9137371663234766401718003)
                ·
                  refine ⟨13706057494852149602577005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137371663234766401718003 13706057494852149602577005)
                  ·
                    refine ⟨5139771560569556100966377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13706057494852149602577005 5139771560569556100966377)
                    ·
                      refine ⟨3854828670427167075724783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139771560569556100966377 3854828670427167075724783)
                      ·
                        rfl

theorem cell23_7507252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_7507252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507252 prefixEnd_7507252 := by exact prefixLift 7507252
  have htrace : WordTrace (prefixWord ++ tailWord_7507252) baseStart_7507252 baseEnd_7507252 := by
    simpa [prefixWord, tailWord_7507252, baseEnd_7507252] using wordTrace_append hprefix tailTrace_7507252
  have hstable : (prefixWord ++ tailWord_7507252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507252).length < 2 ^ (prefixWord ++ tailWord_7507252).sum := by decide
  have hdescent : baseEnd_7507252 < baseStart_7507252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507268 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_7507268 : Nat := 118140960795 + 7507268 * 2 ^ 59
def prefixEnd_7507268 : Nat := 4983230072969 + 3 ^ 40 * 7507268 * 2
def baseEnd_7507268 : Nat := 3854836886117639013124709

theorem tailTrace_7507268 : CollatzResearch.WordTrace tailWord_7507268 prefixEnd_7507268 3854836886117639013124709 := by
  unfold tailWord_7507268
  simp only [CollatzResearch.WordTrace]
  refine ⟨136906279283228825071593229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182541705710971766762124305 136906279283228825071593229)
  ·
    refine ⟨51339854731210809401847461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136906279283228825071593229 51339854731210809401847461)
    ·
      refine ⟨9626222762102026762846399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51339854731210809401847461 9626222762102026762846399)
      ·
        refine ⟨14439334143153040144269599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626222762102026762846399 14439334143153040144269599)
        ·
          refine ⟨21659001214729560216404399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14439334143153040144269599 21659001214729560216404399)
          ·
            refine ⟨32488501822094340324606599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21659001214729560216404399 32488501822094340324606599)
            ·
              refine ⟨48732752733141510486909899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32488501822094340324606599 48732752733141510486909899)
              ·
                refine ⟨73099129099712265730364849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48732752733141510486909899 73099129099712265730364849)
                ·
                  refine ⟨54824346824784199297773637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73099129099712265730364849 54824346824784199297773637)
                  ·
                    refine ⟨10279565029647037368332557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54824346824784199297773637 10279565029647037368332557)
                    ·
                      refine ⟨3854836886117639013124709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10279565029647037368332557 3854836886117639013124709)
                      ·
                        rfl

theorem cell23_7507268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_7507268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507268 prefixEnd_7507268 := by exact prefixLift 7507268
  have htrace : WordTrace (prefixWord ++ tailWord_7507268) baseStart_7507268 baseEnd_7507268 := by
    simpa [prefixWord, tailWord_7507268, baseEnd_7507268] using wordTrace_append hprefix tailTrace_7507268
  have hstable : (prefixWord ++ tailWord_7507268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507268).length < 2 ^ (prefixWord ++ tailWord_7507268).sum := by decide
  have hdescent : baseEnd_7507268 < baseStart_7507268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507281 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_7507281 : Nat := 118140960795 + 7507281 * 2 ^ 59
def prefixEnd_7507281 : Nat := 4983230072969 + 3 ^ 40 * 7507281 * 2
def baseEnd_7507281 : Nat := 3854843561366147462262149

theorem tailTrace_7507281 : CollatzResearch.WordTrace tailWord_7507281 prefixEnd_7507281 3854843561366147462262149 := by
  unfold tailWord_7507281
  simp only [CollatzResearch.WordTrace]
  refine ⟨273813032715410553363409697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182542021810273702242273131 273813032715410553363409697)
  ·
    refine ⟨205359774536557915022557273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273813032715410553363409697 205359774536557915022557273)
    ·
      refine ⟨154019830902418436266917955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205359774536557915022557273 154019830902418436266917955)
      ·
        refine ⟨231029746353627654400376933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154019830902418436266917955 231029746353627654400376933)
        ·
          refine ⟨43318077441305185200070675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231029746353627654400376933 43318077441305185200070675)
          ·
            refine ⟨64977116161957777800106013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43318077441305185200070675 64977116161957777800106013)
            ·
              refine ⟨24366418560734166675039755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64977116161957777800106013 24366418560734166675039755)
              ·
                refine ⟨36549627841101250012559633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24366418560734166675039755 36549627841101250012559633)
                ·
                  refine ⟨27412220880825937509419725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36549627841101250012559633 27412220880825937509419725)
                  ·
                    refine ⟨10279582830309726566032397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27412220880825937509419725 10279582830309726566032397)
                    ·
                      refine ⟨3854843561366147462262149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10279582830309726566032397 3854843561366147462262149)
                      ·
                        rfl

theorem cell23_7507281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_7507281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507281 prefixEnd_7507281 := by exact prefixLift 7507281
  have htrace : WordTrace (prefixWord ++ tailWord_7507281) baseStart_7507281 baseEnd_7507281 := by
    simpa [prefixWord, tailWord_7507281, baseEnd_7507281] using wordTrace_append hprefix tailTrace_7507281
  have hstable : (prefixWord ++ tailWord_7507281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507281).length < 2 ^ (prefixWord ++ tailWord_7507281).sum := by decide
  have hdescent : baseEnd_7507281 < baseStart_7507281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507321 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_7507321 : Nat := 118140960795 + 7507321 * 2 ^ 59
def prefixEnd_7507321 : Nat := 4983230072969 + 3 ^ 40 * 7507321 * 2
def baseEnd_7507321 : Nat := 3854864100592327305761965

theorem tailTrace_7507321 : CollatzResearch.WordTrace tailWord_7507321 prefixEnd_7507321 3854864100592327305761965 := by
  unfold tailWord_7507321
  simp only [CollatzResearch.WordTrace]
  refine ⟨273814491635265640194865817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182542994423510426796577211 273814491635265640194865817)
  ·
    refine ⟨205360868726449230146149363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273814491635265640194865817 205360868726449230146149363)
    ·
      refine ⟨308041303089673845219224045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205360868726449230146149363 308041303089673845219224045)
      ·
        refine ⟨115515488658627691957209017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308041303089673845219224045 115515488658627691957209017)
        ·
          refine ⟨86636616493970768967906763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115515488658627691957209017 86636616493970768967906763)
          ·
            refine ⟨129954924740956153451860145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86636616493970768967906763 129954924740956153451860145)
            ·
              refine ⟨97466193555717115088895109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129954924740956153451860145 97466193555717115088895109)
              ·
                refine ⟨18274911291696959079167833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97466193555717115088895109 18274911291696959079167833)
                ·
                  refine ⟨13706183468772719309375875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18274911291696959079167833 13706183468772719309375875)
                  ·
                    refine ⟨20559275203159078964063813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13706183468772719309375875 20559275203159078964063813)
                    ·
                      refine ⟨3854864100592327305761965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20559275203159078964063813 3854864100592327305761965)
                      ·
                        rfl

theorem cell23_7507321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_7507321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507321 prefixEnd_7507321 := by exact prefixLift 7507321
  have htrace : WordTrace (prefixWord ++ tailWord_7507321) baseStart_7507321 baseEnd_7507321 := by
    simpa [prefixWord, tailWord_7507321, baseEnd_7507321] using wordTrace_append hprefix tailTrace_7507321
  have hstable : (prefixWord ++ tailWord_7507321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507321).length < 2 ^ (prefixWord ++ tailWord_7507321).sum := by decide
  have hdescent : baseEnd_7507321 < baseStart_7507321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507425 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 1, 5]
def baseStart_7507425 : Nat := 118140960795 + 7507425 * 2 ^ 59
def prefixEnd_7507425 : Nat := 4983230072969 + 3 ^ 40 * 7507425 * 2
def baseEnd_7507425 : Nat := 1284972500860131632953829

theorem tailTrace_7507425 : CollatzResearch.WordTrace tailWord_7507425 prefixEnd_7507425 1284972500860131632953829 := by
  unfold tailWord_7507425
  simp only [CollatzResearch.WordTrace]
  refine ⟨273818284826888865956651729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182545523217925910637767819 273818284826888865956651729)
  ·
    refine ⟨205363713620166649467488797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273818284826888865956651729 205363713620166649467488797)
    ·
      refine ⟨77011392607562493550308299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205363713620166649467488797 77011392607562493550308299)
      ·
        refine ⟨115517088911343740325462449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77011392607562493550308299 115517088911343740325462449)
        ·
          refine ⟨86637816683507805244096837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115517088911343740325462449 86637816683507805244096837)
          ·
            refine ⟨16244590628157713483268157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86637816683507805244096837 16244590628157713483268157)
            ·
              refine ⟨6091721485559142556225559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16244590628157713483268157 6091721485559142556225559)
              ·
                refine ⟨9137582228338713834338339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091721485559142556225559 9137582228338713834338339)
                ·
                  refine ⟨13706373342508070751507509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137582228338713834338339 13706373342508070751507509)
                  ·
                    refine ⟨1284972500860131632953829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13706373342508070751507509 1284972500860131632953829)
                    ·
                      rfl

theorem cell23_7507425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_7507425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507425 prefixEnd_7507425 := by exact prefixLift 7507425
  have htrace : WordTrace (prefixWord ++ tailWord_7507425) baseStart_7507425 baseEnd_7507425 := by
    simpa [prefixWord, tailWord_7507425, baseEnd_7507425] using wordTrace_append hprefix tailTrace_7507425
  have hstable : (prefixWord ++ tailWord_7507425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507425).length < 2 ^ (prefixWord ++ tailWord_7507425).sum := by decide
  have hdescent : baseEnd_7507425 < baseStart_7507425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507428 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_7507428 : Nat := 118140960795 + 7507428 * 2 ^ 59
def prefixEnd_7507428 : Nat := 4983230072969 + 3 ^ 40 * 7507428 * 2
def baseEnd_7507428 : Nat := 3854919043022358387123973

theorem tailTrace_7507428 : CollatzResearch.WordTrace tailWord_7507428 prefixEnd_7507428 3854919043022358387123973 := by
  unfold tailWord_7507428
  simp only [CollatzResearch.WordTrace]
  refine ⟨136909197122938998734505469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182545596163918664979340625 136909197122938998734505469)
  ·
    refine ⟨51340948921102124525439551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136909197122938998734505469 51340948921102124525439551)
    ·
      refine ⟨77011423381653186788159327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51340948921102124525439551 77011423381653186788159327)
      ·
        refine ⟨115517135072479780182238991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77011423381653186788159327 115517135072479780182238991)
        ·
          refine ⟨173275702608719670273358487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115517135072479780182238991 173275702608719670273358487)
          ·
            refine ⟨259913553913079505410037731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173275702608719670273358487 259913553913079505410037731)
            ·
              refine ⟨389870330869619258115056597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259913553913079505410037731 389870330869619258115056597)
              ·
                refine ⟨9137585879756701362071639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 389870330869619258115056597 9137585879756701362071639)
                ·
                  refine ⟨13706378819635052043107459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137585879756701362071639 13706378819635052043107459)
                  ·
                    refine ⟨20559568229452578064661189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13706378819635052043107459 20559568229452578064661189)
                    ·
                      refine ⟨3854919043022358387123973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20559568229452578064661189 3854919043022358387123973)
                      ·
                        rfl

theorem cell23_7507428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_7507428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507428 prefixEnd_7507428 := by exact prefixLift 7507428
  have htrace : WordTrace (prefixWord ++ tailWord_7507428) baseStart_7507428 baseEnd_7507428 := by
    simpa [prefixWord, tailWord_7507428, baseEnd_7507428] using wordTrace_append hprefix tailTrace_7507428
  have hstable : (prefixWord ++ tailWord_7507428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507428).length < 2 ^ (prefixWord ++ tailWord_7507428).sum := by decide
  have hdescent : baseEnd_7507428 < baseStart_7507428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507445 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7507445 : Nat := 118140960795 + 7507445 * 2 ^ 59
def prefixEnd_7507445 : Nat := 4983230072969 + 3 ^ 40 * 7507445 * 2
def baseEnd_7507445 : Nat := 3854927772193484820611395

theorem tailTrace_7507445 : CollatzResearch.WordTrace tailWord_7507445 prefixEnd_7507445 3854927772193484820611395 := by
  unfold tailWord_7507445
  simp only [CollatzResearch.WordTrace]
  refine ⟨273819014286816409372379789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182546009524544272914919859 273819014286816409372379789)
  ·
    refine ⟨102682130357556153514642421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273819014286816409372379789 102682130357556153514642421)
    ·
      refine ⟨9626449721020889391997727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102682130357556153514642421 9626449721020889391997727)
      ·
        refine ⟨14439674581531334087996591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626449721020889391997727 14439674581531334087996591)
        ·
          refine ⟨21659511872297001131994887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14439674581531334087996591 21659511872297001131994887)
          ·
            refine ⟨32489267808445501697992331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21659511872297001131994887 32489267808445501697992331)
            ·
              refine ⟨48733901712668252546988497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32489267808445501697992331 48733901712668252546988497)
              ·
                refine ⟨36550426284501189410241373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48733901712668252546988497 36550426284501189410241373)
                ·
                  refine ⟨13706409856687946028840515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36550426284501189410241373 13706409856687946028840515)
                  ·
                    refine ⟨20559614785031919043260773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13706409856687946028840515 20559614785031919043260773)
                    ·
                      refine ⟨3854927772193484820611395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20559614785031919043260773 3854927772193484820611395)
                      ·
                        rfl

theorem cell23_7507445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7507445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507445 prefixEnd_7507445 := by exact prefixLift 7507445
  have htrace : WordTrace (prefixWord ++ tailWord_7507445) baseStart_7507445 baseEnd_7507445 := by
    simpa [prefixWord, tailWord_7507445, baseEnd_7507445] using wordTrace_append hprefix tailTrace_7507445
  have hstable : (prefixWord ++ tailWord_7507445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507445).length < 2 ^ (prefixWord ++ tailWord_7507445).sum := by decide
  have hdescent : baseEnd_7507445 < baseStart_7507445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507448 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_7507448 : Nat := 118140960795 + 7507448 * 2 ^ 59
def prefixEnd_7507448 : Nat := 4983230072969 + 3 ^ 40 * 7507448 * 2
def baseEnd_7507448 : Nat := 3854929312635448308873881

theorem tailTrace_7507448 : CollatzResearch.WordTrace tailWord_7507448 prefixEnd_7507448 3854929312635448308873881 := by
  unfold tailWord_7507448
  simp only [CollatzResearch.WordTrace]
  refine ⟨136909561852902770442369499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182546082470537027256492665 136909561852902770442369499)
  ·
    refine ⟨205364342779354155663554249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136909561852902770442369499 205364342779354155663554249)
    ·
      refine ⟨154023257084515616747665687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205364342779354155663554249 154023257084515616747665687)
      ·
        refine ⟨231034885626773425121498531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154023257084515616747665687 231034885626773425121498531)
        ·
          refine ⟨346552328440160137682247797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231034885626773425121498531 346552328440160137682247797)
          ·
            refine ⟨32489280791265012907710731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 346552328440160137682247797 32489280791265012907710731)
            ·
              refine ⟨48733921186897519361566097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32489280791265012907710731 48733921186897519361566097)
              ·
                refine ⟨36550440890173139521174573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48733921186897519361566097 36550440890173139521174573)
                ·
                  refine ⟨13706415333814927320440465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36550440890173139521174573 13706415333814927320440465)
                  ·
                    refine ⟨10279811500361195490330349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13706415333814927320440465 10279811500361195490330349)
                    ·
                      refine ⟨3854929312635448308873881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10279811500361195490330349 3854929312635448308873881)
                      ·
                        rfl

theorem cell23_7507448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_7507448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507448 prefixEnd_7507448 := by exact prefixLift 7507448
  have htrace : WordTrace (prefixWord ++ tailWord_7507448) baseStart_7507448 baseEnd_7507448 := by
    simpa [prefixWord, tailWord_7507448, baseEnd_7507448] using wordTrace_append hprefix tailTrace_7507448
  have hstable : (prefixWord ++ tailWord_7507448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507448).length < 2 ^ (prefixWord ++ tailWord_7507448).sum := by decide
  have hdescent : baseEnd_7507448 < baseStart_7507448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507476 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_7507476 : Nat := 118140960795 + 7507476 * 2 ^ 59
def prefixEnd_7507476 : Nat := 4983230072969 + 3 ^ 40 * 7507476 * 2
def baseEnd_7507476 : Nat := 1284981230031258066441251

theorem tailTrace_7507476 : CollatzResearch.WordTrace tailWord_7507476 prefixEnd_7507476 1284981230031258066441251 := by
  unfold tailWord_7507476
  simp only [CollatzResearch.WordTrace]
  refine ⟨136910072474852050833379141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182546763299802734444505521 136910072474852050833379141)
  ·
    refine ⟨25670638589034759531258589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136910072474852050833379141 25670638589034759531258589)
    ·
      refine ⟨9626489470888034824221971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25670638589034759531258589 9626489470888034824221971)
      ·
        refine ⟨14439734206332052236332957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626489470888034824221971 14439734206332052236332957)
        ·
          refine ⟨5414900327374519588624859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14439734206332052236332957 5414900327374519588624859)
          ·
            refine ⟨8122350491061779382937289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414900327374519588624859 8122350491061779382937289)
            ·
              refine ⟨6091762868296334537202967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8122350491061779382937289 6091762868296334537202967)
              ·
                refine ⟨9137644302444501805804451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091762868296334537202967 9137644302444501805804451)
                ·
                  refine ⟨13706466453666752708706677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137644302444501805804451 13706466453666752708706677)
                  ·
                    refine ⟨1284981230031258066441251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13706466453666752708706677 1284981230031258066441251)
                    ·
                      rfl

theorem cell23_7507476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_7507476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507476 prefixEnd_7507476 := by exact prefixLift 7507476
  have htrace : WordTrace (prefixWord ++ tailWord_7507476) baseStart_7507476 baseEnd_7507476 := by
    simpa [prefixWord, tailWord_7507476, baseEnd_7507476] using wordTrace_append hprefix tailTrace_7507476
  have hstable : (prefixWord ++ tailWord_7507476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507476).length < 2 ^ (prefixWord ++ tailWord_7507476).sum := by decide
  have hdescent : baseEnd_7507476 < baseStart_7507476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507538 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_7507538 : Nat := 118140960795 + 7507538 * 2 ^ 59
def prefixEnd_7507538 : Nat := 4983230072969 + 3 ^ 40 * 7507538 * 2
def baseEnd_7507538 : Nat := 3854975525894352956748467

theorem tailTrace_7507538 : CollatzResearch.WordTrace tailWord_7507538 prefixEnd_7507538 3854975525894352956748467 := by
  unfold tailWord_7507538
  simp only [CollatzResearch.WordTrace]
  refine ⟨68455601568869871563878817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182548270850319657503676845 68455601568869871563878817)
  ·
    refine ⟨51341701176652403672909113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68455601568869871563878817 51341701176652403672909113)
    ·
      refine ⟨38506275882489302754681835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51341701176652403672909113 38506275882489302754681835)
      ·
        refine ⟨57759413823733954132022753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38506275882489302754681835 57759413823733954132022753)
        ·
          refine ⟨43319560367800465599017065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57759413823733954132022753 43319560367800465599017065)
          ·
            refine ⟨32489670275850349199262799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43319560367800465599017065 32489670275850349199262799)
            ·
              refine ⟨48734505413775523798894199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32489670275850349199262799 48734505413775523798894199)
              ·
                refine ⟨73101758120663285698341299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48734505413775523798894199 73101758120663285698341299)
                ·
                  refine ⟨109652637180994928547511949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73101758120663285698341299 109652637180994928547511949)
                  ·
                    refine ⟨41119738942873098205316981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109652637180994928547511949 41119738942873098205316981)
                    ·
                      refine ⟨3854975525894352956748467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41119738942873098205316981 3854975525894352956748467)
                      ·
                        rfl

theorem cell23_7507538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_7507538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507538 prefixEnd_7507538 := by exact prefixLift 7507538
  have htrace : WordTrace (prefixWord ++ tailWord_7507538) baseStart_7507538 baseEnd_7507538 := by
    simpa [prefixWord, tailWord_7507538, baseEnd_7507538] using wordTrace_append hprefix tailTrace_7507538
  have hstable : (prefixWord ++ tailWord_7507538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507538).length < 2 ^ (prefixWord ++ tailWord_7507538).sum := by decide
  have hdescent : baseEnd_7507538 < baseStart_7507538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507552 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 2, 2, 2]
def baseStart_7507552 : Nat := 118140960795 + 7507552 * 2 ^ 59
def prefixEnd_7507552 : Nat := 4983230072969 + 3 ^ 40 * 7507552 * 2
def baseEnd_7507552 : Nat := 3854982714623515901973403

theorem tailTrace_7507552 : CollatzResearch.WordTrace tailWord_7507552 prefixEnd_7507552 3854982714623515901973403 := by
  unfold tailWord_7507552
  simp only [CollatzResearch.WordTrace]
  refine ⟨136911458448714383323262455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182548611264952511097683273 136911458448714383323262455)
  ·
    refine ⟨205367187673071574984893683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136911458448714383323262455 205367187673071574984893683)
    ·
      refine ⟨308050781509607362477340525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205367187673071574984893683 308050781509607362477340525)
      ·
        refine ⟨115519043066102760929002697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308050781509607362477340525 115519043066102760929002697)
        ·
          refine ⟨86639282299577070696752023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115519043066102760929002697 86639282299577070696752023)
          ·
            refine ⟨129958923449365606045128035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86639282299577070696752023 129958923449365606045128035)
            ·
              refine ⟨194938385174048409067692053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129958923449365606045128035 194938385174048409067692053)
              ·
                refine ⟨9137736805033519175048065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194938385174048409067692053 9137736805033519175048065)
                ·
                  refine ⟨6853302603775139381286049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9137736805033519175048065 6853302603775139381286049)
                  ·
                    refine ⟨5139976952831354535964537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6853302603775139381286049 5139976952831354535964537)
                    ·
                      refine ⟨3854982714623515901973403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5139976952831354535964537 3854982714623515901973403)
                      ·
                        rfl

theorem cell23_7507552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_7507552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507552 prefixEnd_7507552 := by exact prefixLift 7507552
  have htrace : WordTrace (prefixWord ++ tailWord_7507552) baseStart_7507552 baseEnd_7507552 := by
    simpa [prefixWord, tailWord_7507552, baseEnd_7507552] using wordTrace_append hprefix tailTrace_7507552
  have hstable : (prefixWord ++ tailWord_7507552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507552).length < 2 ^ (prefixWord ++ tailWord_7507552).sum := by decide
  have hdescent : baseEnd_7507552 < baseStart_7507552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507635 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 3, 4]
def baseStart_7507635 : Nat := 118140960795 + 7507635 * 2 ^ 59
def prefixEnd_7507635 : Nat := 4983230072969 + 3 ^ 40 * 7507635 * 2
def baseEnd_7507635 : Nat := 1285008444505946359078507

theorem tailTrace_7507635 : CollatzResearch.WordTrace tailWord_7507635 prefixEnd_7507635 1285008444505946359078507 := by
  unfold tailWord_7507635
  simp only [CollatzResearch.WordTrace]
  refine ⟨273825944156128071821796359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182550629437418714547864239 273825944156128071821796359)
  ·
    refine ⟨410738916234192107732694539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273825944156128071821796359 410738916234192107732694539)
    ·
      refine ⟨616108374351288161599041809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410738916234192107732694539 616108374351288161599041809)
      ·
        refine ⟨462081280763466121199281357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616108374351288161599041809 462081280763466121199281357)
        ·
          refine ⟨173280480286299795449730509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462081280763466121199281357 173280480286299795449730509)
          ·
            refine ⟨64980180107362423293648941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173280480286299795449730509 64980180107362423293648941)
            ·
              refine ⟨24367567540260908735118353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64980180107362423293648941 24367567540260908735118353)
              ·
                refine ⟨18275675655195681551338765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24367567540260908735118353 18275675655195681551338765)
                ·
                  refine ⟨6853378370698380581752037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18275675655195681551338765 6853378370698380581752037)
                  ·
                    refine ⟨1285008444505946359078507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6853378370698380581752037 1285008444505946359078507)
                    ·
                      rfl

theorem cell23_7507635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 4].length) (baseStart_7507635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507635 prefixEnd_7507635 := by exact prefixLift 7507635
  have htrace : WordTrace (prefixWord ++ tailWord_7507635) baseStart_7507635 baseEnd_7507635 := by
    simpa [prefixWord, tailWord_7507635, baseEnd_7507635] using wordTrace_append hprefix tailTrace_7507635
  have hstable : (prefixWord ++ tailWord_7507635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507635).length < 2 ^ (prefixWord ++ tailWord_7507635).sum := by decide
  have hdescent : baseEnd_7507635 < baseStart_7507635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507642 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4]
def baseStart_7507642 : Nat := 118140960795 + 7507642 * 2 ^ 59
def prefixEnd_7507642 : Nat := 4983230072969 + 3 ^ 40 * 7507642 * 2
def baseEnd_7507642 : Nat := 3855028927882420549847989

theorem tailTrace_7507642 : CollatzResearch.WordTrace tailWord_7507642 prefixEnd_7507642 3855028927882420549847989 := by
  unfold tailWord_7507642
  simp only [CollatzResearch.WordTrace]
  refine ⟨68456549866775678004325295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182550799644735141344867453 68456549866775678004325295)
  ·
    refine ⟨102684824800163517006487943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68456549866775678004325295 102684824800163517006487943)
    ·
      refine ⟨154027237200245275509731915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102684824800163517006487943 154027237200245275509731915)
      ·
        refine ⟨231040855800367913264597873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154027237200245275509731915 231040855800367913264597873)
        ·
          refine ⟨173280641850275934948448405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231040855800367913264597873 173280641850275934948448405)
          ·
            refine ⟨8122530086731684450708519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173280641850275934948448405 8122530086731684450708519)
            ·
              refine ⟨12183795130097526676062779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122530086731684450708519 12183795130097526676062779)
              ·
                refine ⟨18275692695146290014094169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12183795130097526676062779 18275692695146290014094169)
                ·
                  refine ⟨13706769521359717510570627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18275692695146290014094169 13706769521359717510570627)
                  ·
                    refine ⟨20560154282039576265855941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13706769521359717510570627 20560154282039576265855941)
                    ·
                      refine ⟨3855028927882420549847989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20560154282039576265855941 3855028927882420549847989)
                      ·
                        rfl

theorem cell23_7507642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_7507642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507642 prefixEnd_7507642 := by exact prefixLift 7507642
  have htrace : WordTrace (prefixWord ++ tailWord_7507642) baseStart_7507642 baseEnd_7507642 := by
    simpa [prefixWord, tailWord_7507642, baseEnd_7507642] using wordTrace_append hprefix tailTrace_7507642
  have hstable : (prefixWord ++ tailWord_7507642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507642).length < 2 ^ (prefixWord ++ tailWord_7507642).sum := by decide
  have hdescent : baseEnd_7507642 < baseStart_7507642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507645 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_7507645 : Nat := 118140960795 + 7507645 * 2 ^ 59
def prefixEnd_7507645 : Nat := 4983230072969 + 3 ^ 40 * 7507645 * 2
def baseEnd_7507645 : Nat := 3855030468324384038110475

theorem tailTrace_7507645 : CollatzResearch.WordTrace tailWord_7507645 prefixEnd_7507645 3855030468324384038110475 := by
  unfold tailWord_7507645
  simp only [CollatzResearch.WordTrace]
  refine ⟨273826308886091843529660389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182550872590727895686440259 273826308886091843529660389)
  ·
    refine ⟨51342432916142220661811323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273826308886091843529660389 51342432916142220661811323)
    ·
      refine ⟨77013649374213330992716985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51342432916142220661811323 77013649374213330992716985)
      ·
        refine ⟨57760237030659998244537739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77013649374213330992716985 57760237030659998244537739)
        ·
          refine ⟨86640355545989997366806609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57760237030659998244537739 86640355545989997366806609)
          ·
            refine ⟨64980266659492498025104957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86640355545989997366806609 64980266659492498025104957)
            ·
              refine ⟨24367599997309686759414359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64980266659492498025104957 24367599997309686759414359)
              ·
                refine ⟨36551399995964530139121539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24367599997309686759414359 36551399995964530139121539)
                ·
                  refine ⟨54827099993946795208682309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36551399995964530139121539 54827099993946795208682309)
                  ·
                    refine ⟨10280081248865024101627933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54827099993946795208682309 10280081248865024101627933)
                    ·
                      refine ⟨3855030468324384038110475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10280081248865024101627933 3855030468324384038110475)
                      ·
                        rfl

theorem cell23_7507645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_7507645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507645 prefixEnd_7507645 := by exact prefixLift 7507645
  have htrace : WordTrace (prefixWord ++ tailWord_7507645) baseStart_7507645 baseEnd_7507645 := by
    simpa [prefixWord, tailWord_7507645, baseEnd_7507645] using wordTrace_append hprefix tailTrace_7507645
  have hstable : (prefixWord ++ tailWord_7507645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507645).length < 2 ^ (prefixWord ++ tailWord_7507645).sum := by decide
  have hdescent : baseEnd_7507645 < baseStart_7507645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507648 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 8]
def baseStart_7507648 : Nat := 118140960795 + 7507648 * 2 ^ 59
def prefixEnd_7507648 : Nat := 4983230072969 + 3 ^ 40 * 7507648 * 2
def baseEnd_7507648 : Nat := 428336889862927502930329

theorem tailTrace_7507648 : CollatzResearch.WordTrace tailWord_7507648 prefixEnd_7507648 428336889862927502930329 := by
  unfold tailWord_7507648
  simp only [CollatzResearch.WordTrace]
  refine ⟨136913209152540487521009799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182550945536720650028013065 136913209152540487521009799)
  ·
    refine ⟨205369813728810731281514699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136913209152540487521009799 205369813728810731281514699)
    ·
      refine ⟨308054720593216096922272049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205369813728810731281514699 308054720593216096922272049)
      ·
        refine ⟨231041040444912072691704037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308054720593216096922272049 231041040444912072691704037)
        ·
          refine ⟨43320195083421013629694507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231041040444912072691704037 43320195083421013629694507)
          ·
            refine ⟨64980292625131520444541761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43320195083421013629694507 64980292625131520444541761)
            ·
              refine ⟨48735219468848640333406321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64980292625131520444541761 48735219468848640333406321)
              ·
                refine ⟨36551414601636480250054741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48735219468848640333406321 36551414601636480250054741)
                ·
                  refine ⟨428336889862927502930329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36551414601636480250054741 428336889862927502930329)
                  ·
                    rfl

theorem cell23_7507648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 8].length) (baseStart_7507648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507648 prefixEnd_7507648 := by exact prefixLift 7507648
  have htrace : WordTrace (prefixWord ++ tailWord_7507648) baseStart_7507648 baseEnd_7507648 := by
    simpa [prefixWord, tailWord_7507648, baseEnd_7507648] using wordTrace_append hprefix tailTrace_7507648
  have hstable : (prefixWord ++ tailWord_7507648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507648).length < 2 ^ (prefixWord ++ tailWord_7507648).sum := by decide
  have hdescent : baseEnd_7507648 < baseStart_7507648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507665 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 6]
def baseStart_7507665 : Nat := 118140960795 + 7507665 * 2 ^ 59
def prefixEnd_7507665 : Nat := 4983230072969 + 3 ^ 40 * 7507665 * 2
def baseEnd_7507665 : Nat := 428337859770830439984487

theorem tailTrace_7507665 : CollatzResearch.WordTrace tailWord_7507665 prefixEnd_7507665 428337859770830439984487 := by
  unfold tailWord_7507665
  simp only [CollatzResearch.WordTrace]
  refine ⟨273827038346019386945388449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182551358897346257963592299 273827038346019386945388449)
  ·
    refine ⟨205370278759514540209041337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273827038346019386945388449 205370278759514540209041337)
    ·
      refine ⟨154027709069635905156781003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205370278759514540209041337 154027709069635905156781003)
      ·
        refine ⟨231041563604453857735171505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154027709069635905156781003 231041563604453857735171505)
        ·
          refine ⟨173281172703340393301378629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231041563604453857735171505 173281172703340393301378629)
          ·
            refine ⟨32490219881876323744008493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173281172703340393301378629 32490219881876323744008493)
            ·
              refine ⟨12183832455703621404003185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32490219881876323744008493 12183832455703621404003185)
              ·
                refine ⟨9137874341777716053002389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12183832455703621404003185 9137874341777716053002389)
                ·
                  refine ⟨428337859770830439984487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9137874341777716053002389 428337859770830439984487)
                  ·
                    rfl

theorem cell23_7507665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 6].length) (baseStart_7507665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507665 prefixEnd_7507665 := by exact prefixLift 7507665
  have htrace : WordTrace (prefixWord ++ tailWord_7507665) baseStart_7507665 baseEnd_7507665 := by
    simpa [prefixWord, tailWord_7507665, baseEnd_7507665] using wordTrace_append hprefix tailTrace_7507665
  have hstable : (prefixWord ++ tailWord_7507665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507665).length < 2 ^ (prefixWord ++ tailWord_7507665).sum := by decide
  have hdescent : baseEnd_7507665 < baseStart_7507665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507692 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 3]
def baseStart_7507692 : Nat := 118140960795 + 7507692 * 2 ^ 59
def prefixEnd_7507692 : Nat := 4983230072969 + 3 ^ 40 * 7507692 * 2
def baseEnd_7507692 : Nat := 3855054601915145354222759

theorem tailTrace_7507692 : CollatzResearch.WordTrace tailWord_7507692 prefixEnd_7507692 3855054601915145354222759 := by
  unfold tailWord_7507692
  simp only [CollatzResearch.WordTrace]
  refine ⟨136914011558460785278310665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182552015411281047037747553 136914011558460785278310665)
  ·
    refine ⟨102685508668845588958732999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136914011558460785278310665 102685508668845588958732999)
    ·
      refine ⟨154028263003268383438099499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102685508668845588958732999 154028263003268383438099499)
      ·
        refine ⟨231042394504902575157149249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154028263003268383438099499 231042394504902575157149249)
        ·
          refine ⟨173281795878676931367861937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231042394504902575157149249 173281795878676931367861937)
          ·
            refine ⟨129961346909007698525896453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173281795878676931367861937 129961346909007698525896453)
            ·
              refine ⟨24367752545438943473605585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129961346909007698525896453 24367752545438943473605585)
              ·
                refine ⟨18275814409079207605204189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24367752545438943473605585 18275814409079207605204189)
                ·
                  refine ⟨6853430403404702851951571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18275814409079207605204189 6853430403404702851951571)
                  ·
                    refine ⟨10280145605107054277927357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6853430403404702851951571 10280145605107054277927357)
                    ·
                      refine ⟨3855054601915145354222759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10280145605107054277927357 3855054601915145354222759)
                      ·
                        rfl

theorem cell23_7507692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_7507692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507692 prefixEnd_7507692 := by exact prefixLift 7507692
  have htrace : WordTrace (prefixWord ++ tailWord_7507692) baseStart_7507692 baseEnd_7507692 := by
    simpa [prefixWord, tailWord_7507692, baseEnd_7507692] using wordTrace_append hprefix tailTrace_7507692
  have hstable : (prefixWord ++ tailWord_7507692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507692).length < 2 ^ (prefixWord ++ tailWord_7507692).sum := by decide
  have hdescent : baseEnd_7507692 < baseStart_7507692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507709 : List Nat := [1, 4, 1, 1, 1, 1, 2, 7, 1, 1, 3]
def baseStart_7507709 : Nat := 118140960795 + 7507709 * 2 ^ 59
def prefixEnd_7507709 : Nat := 4983230072969 + 3 ^ 40 * 7507709 * 2
def baseEnd_7507709 : Nat := 3855063331086271787710181

theorem tailTrace_7507709 : CollatzResearch.WordTrace tailWord_7507709 prefixEnd_7507709 3855063331086271787710181 := by
  unfold tailWord_7507709
  simp only [CollatzResearch.WordTrace]
  refine ⟨273828643157859982459990181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182552428771906654973326787 273828643157859982459990181)
  ·
    refine ⟨51342870592098746711248159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273828643157859982459990181 51342870592098746711248159)
    ·
      refine ⟨77014305888148120066872239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51342870592098746711248159 77014305888148120066872239)
      ·
        refine ⟨115521458832222180100308359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77014305888148120066872239 115521458832222180100308359)
        ·
          refine ⟨173282188248333270150462539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115521458832222180100308359 173282188248333270150462539)
          ·
            refine ⟨259923282372499905225693809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173282188248333270150462539 259923282372499905225693809)
            ·
              refine ⟨194942461779374928919270357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259923282372499905225693809 194942461779374928919270357)
              ·
                refine ⟨4568963947954099896545399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194942461779374928919270357 4568963947954099896545399)
                ·
                  refine ⟨6853445921931149844818099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568963947954099896545399 6853445921931149844818099)
                  ·
                    refine ⟨10280168882896724767227149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6853445921931149844818099 10280168882896724767227149)
                    ·
                      refine ⟨3855063331086271787710181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10280168882896724767227149 3855063331086271787710181)
                      ·
                        rfl

theorem cell23_7507709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_7507709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507709 prefixEnd_7507709 := by exact prefixLift 7507709
  have htrace : WordTrace (prefixWord ++ tailWord_7507709) baseStart_7507709 baseEnd_7507709 := by
    simpa [prefixWord, tailWord_7507709, baseEnd_7507709] using wordTrace_append hprefix tailTrace_7507709
  have hstable : (prefixWord ++ tailWord_7507709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507709).length < 2 ^ (prefixWord ++ tailWord_7507709).sum := by decide
  have hdescent : baseEnd_7507709 < baseStart_7507709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507745 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_7507745 : Nat := 118140960795 + 7507745 * 2 ^ 59
def prefixEnd_7507745 : Nat := 4983230072969 + 3 ^ 40 * 7507745 * 2
def baseEnd_7507745 : Nat := 3855081816389833646860015

theorem tailTrace_7507745 : CollatzResearch.WordTrace tailWord_7507745 prefixEnd_7507745 3855081816389833646860015 := by
  unfold tailWord_7507745
  simp only [CollatzResearch.WordTrace]
  refine ⟨273829956185729560608300689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182553304123819707072200459 273829956185729560608300689)
  ·
    refine ⟨205372467139297170456225517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273829956185729560608300689 205372467139297170456225517)
    ·
      refine ⟨77014675177236438921084569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205372467139297170456225517 77014675177236438921084569)
      ·
        refine ⟨57761006382927329190813427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77014675177236438921084569 57761006382927329190813427)
        ·
          refine ⟨86641509574390993786220141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57761006382927329190813427 86641509574390993786220141)
          ·
            refine ⟨32490566090396622669832553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86641509574390993786220141 32490566090396622669832553)
            ·
              refine ⟨24367924567797467002374415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32490566090396622669832553 24367924567797467002374415)
              ·
                refine ⟨36551886851696200503561623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24367924567797467002374415 36551886851696200503561623)
                ·
                  refine ⟨54827830277544300755342435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36551886851696200503561623 54827830277544300755342435)
                  ·
                    refine ⟨82241745416316451133013653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54827830277544300755342435 82241745416316451133013653)
                    ·
                      refine ⟨3855081816389833646860015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82241745416316451133013653 3855081816389833646860015)
                      ·
                        rfl

theorem cell23_7507745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_7507745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507745 prefixEnd_7507745 := by exact prefixLift 7507745
  have htrace : WordTrace (prefixWord ++ tailWord_7507745) baseStart_7507745 baseEnd_7507745 := by
    simpa [prefixWord, tailWord_7507745, baseEnd_7507745] using wordTrace_append hprefix tailTrace_7507745
  have hstable : (prefixWord ++ tailWord_7507745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507745).length < 2 ^ (prefixWord ++ tailWord_7507745).sum := by decide
  have hdescent : baseEnd_7507745 < baseStart_7507745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507749 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 4]
def baseStart_7507749 : Nat := 118140960795 + 7507749 * 2 ^ 59
def prefixEnd_7507749 : Nat := 4983230072969 + 3 ^ 40 * 7507749 * 2
def baseEnd_7507749 : Nat := 3855083870312451631209997

theorem tailTrace_7507749 : CollatzResearch.WordTrace tailWord_7507749 prefixEnd_7507749 3855083870312451631209997 := by
  unfold tailWord_7507749
  simp only [CollatzResearch.WordTrace]
  refine ⟨273830102077715069291446301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182553401385143379527630867 273830102077715069291446301)
  ·
    refine ⟨102686288279143150984292363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273830102077715069291446301 102686288279143150984292363)
    ·
      refine ⟨154029432418714726476438545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102686288279143150984292363 154029432418714726476438545)
      ·
        refine ⟨115522074314036044857328909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154029432418714726476438545 115522074314036044857328909)
        ·
          refine ⟨43320777867763516821498341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115522074314036044857328909 43320777867763516821498341)
          ·
            refine ⟨8122645850205659404030939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43320777867763516821498341 8122645850205659404030939)
            ·
              refine ⟨12183968775308489106046409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122645850205659404030939 12183968775308489106046409)
              ·
                refine ⟨9137976581481366829534807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12183968775308489106046409 9137976581481366829534807)
                ·
                  refine ⟨13706964872222050244302211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137976581481366829534807 13706964872222050244302211)
                  ·
                    refine ⟨20560447308333075366453317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13706964872222050244302211 20560447308333075366453317)
                    ·
                      refine ⟨3855083870312451631209997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20560447308333075366453317 3855083870312451631209997)
                      ·
                        rfl

theorem cell23_7507749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_7507749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507749 prefixEnd_7507749 := by exact prefixLift 7507749
  have htrace : WordTrace (prefixWord ++ tailWord_7507749) baseStart_7507749 baseEnd_7507749 := by
    simpa [prefixWord, tailWord_7507749, baseEnd_7507749] using wordTrace_append hprefix tailTrace_7507749
  have hstable : (prefixWord ++ tailWord_7507749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507749).length < 2 ^ (prefixWord ++ tailWord_7507749).sum := by decide
  have hdescent : baseEnd_7507749 < baseStart_7507749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507762 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_7507762 : Nat := 118140960795 + 7507762 * 2 ^ 59
def prefixEnd_7507762 : Nat := 4983230072969 + 3 ^ 40 * 7507762 * 2
def baseEnd_7507762 : Nat := 3855090545560960080347437

theorem tailTrace_7507762 : CollatzResearch.WordTrace tailWord_7507762 prefixEnd_7507762 3855090545560960080347437 := by
  unfold tailWord_7507762
  simp only [CollatzResearch.WordTrace]
  refine ⟨68457644056666993127917385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182553717484445315007779693 68457644056666993127917385)
  ·
    refine ⟨51343233042500244845938039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68457644056666993127917385 51343233042500244845938039)
    ·
      refine ⟨77014849563750367268907059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51343233042500244845938039 77014849563750367268907059)
      ·
        refine ⟨115522274345625550903360589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77014849563750367268907059 115522274345625550903360589)
        ·
          refine ⟨43320852879609581588760221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115522274345625550903360589 43320852879609581588760221)
          ·
            refine ⟨16245319829853593095785083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43320852879609581588760221 16245319829853593095785083)
            ·
              refine ⟨24367979744780389643677625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16245319829853593095785083 24367979744780389643677625)
              ·
                refine ⟨18275984808585292232758219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24367979744780389643677625 18275984808585292232758219)
                ·
                  refine ⟨27413977212877938349137329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18275984808585292232758219 27413977212877938349137329)
                  ·
                    refine ⟨20560482909658453761852997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27413977212877938349137329 20560482909658453761852997)
                    ·
                      refine ⟨3855090545560960080347437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20560482909658453761852997 3855090545560960080347437)
                      ·
                        rfl

theorem cell23_7507762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_7507762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507762 prefixEnd_7507762 := by exact prefixLift 7507762
  have htrace : WordTrace (prefixWord ++ tailWord_7507762) baseStart_7507762 baseEnd_7507762 := by
    simpa [prefixWord, tailWord_7507762, baseEnd_7507762] using wordTrace_append hprefix tailTrace_7507762
  have hstable : (prefixWord ++ tailWord_7507762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507762).length < 2 ^ (prefixWord ++ tailWord_7507762).sum := by decide
  have hdescent : baseEnd_7507762 < baseStart_7507762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507783 : List Nat := [1, 1, 4, 1, 2, 1, 6, 2, 1, 2, 2]
def baseStart_7507783 : Nat := 118140960795 + 7507783 * 2 ^ 59
def prefixEnd_7507783 : Nat := 4983230072969 + 3 ^ 40 * 7507783 * 2
def baseEnd_7507783 : Nat := 3855101328654704498184841

theorem tailTrace_7507783 : CollatzResearch.WordTrace tailWord_7507783 prefixEnd_7507783 3855101328654704498184841 := by
  unfold tailWord_7507783
  simp only [CollatzResearch.WordTrace]
  refine ⟨273831342159591893098184003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182554228106394595398789335 273831342159591893098184003)
  ·
    refine ⟨410747013239387839647276005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273831342159591893098184003 410747013239387839647276005)
    ·
      refine ⟨77015064982385219933864251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410747013239387839647276005 77015064982385219933864251)
      ·
        refine ⟨115522597473577829900796377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77015064982385219933864251 115522597473577829900796377)
        ·
          refine ⟨86641948105183372425597283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115522597473577829900796377 86641948105183372425597283)
          ·
            refine ⟨129962922157775058638395925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86641948105183372425597283 129962922157775058638395925)
            ·
              refine ⟨6092011976145705873674809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129962922157775058638395925 6092011976145705873674809)
              ·
                refine ⟨4569008982109279405256107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6092011976145705873674809 4569008982109279405256107)
                ·
                  refine ⟨6853513473163919107884161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569008982109279405256107 6853513473163919107884161)
                  ·
                    refine ⟨5140135104872939330913121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6853513473163919107884161 5140135104872939330913121)
                    ·
                      refine ⟨3855101328654704498184841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140135104872939330913121 3855101328654704498184841)
                      ·
                        rfl

theorem cell23_7507783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_7507783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507783 prefixEnd_7507783 := by exact prefixLift 7507783
  have htrace : WordTrace (prefixWord ++ tailWord_7507783) baseStart_7507783 baseEnd_7507783 := by
    simpa [prefixWord, tailWord_7507783, baseEnd_7507783] using wordTrace_append hprefix tailTrace_7507783
  have hstable : (prefixWord ++ tailWord_7507783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507783).length < 2 ^ (prefixWord ++ tailWord_7507783).sum := by decide
  have hdescent : baseEnd_7507783 < baseStart_7507783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507789 : List Nat := [1, 6, 1, 2, 1, 3, 1, 8]
def baseStart_7507789 : Nat := 118140960795 + 7507789 * 2 ^ 59
def prefixEnd_7507789 : Nat := 4983230072969 + 3 ^ 40 * 7507789 * 2
def baseEnd_7507789 : Nat := 142781644797727091655919

theorem tailTrace_7507789 : CollatzResearch.WordTrace tailWord_7507789 prefixEnd_7507789 142781644797727091655919 := by
  unfold tailWord_7507789
  simp only [CollatzResearch.WordTrace]
  refine ⟨273831560997570156122902421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182554373998380104081934947 273831560997570156122902421)
  ·
    refine ⟨12835854421761101068261051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 273831560997570156122902421 12835854421761101068261051)
    ·
      refine ⟨19253781632641651602391577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12835854421761101068261051 19253781632641651602391577)
      ·
        refine ⟨14440336224481238701793683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19253781632641651602391577 14440336224481238701793683)
        ·
          refine ⟨21660504336721858052690525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14440336224481238701793683 21660504336721858052690525)
          ·
            refine ⟨8122689126270696769758947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21660504336721858052690525 8122689126270696769758947)
            ·
              refine ⟨12184033689406045154638421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122689126270696769758947 12184033689406045154638421)
              ·
                refine ⟨142781644797727091655919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12184033689406045154638421 142781644797727091655919)
                ·
                  rfl

theorem cell23_7507789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 8].length) (baseStart_7507789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507789 prefixEnd_7507789 := by exact prefixLift 7507789
  have htrace : WordTrace (prefixWord ++ tailWord_7507789) baseStart_7507789 baseEnd_7507789 := by
    simpa [prefixWord, tailWord_7507789, baseEnd_7507789] using wordTrace_append hprefix tailTrace_7507789
  have hstable : (prefixWord ++ tailWord_7507789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507789).length < 2 ^ (prefixWord ++ tailWord_7507789).sum := by decide
  have hdescent : baseEnd_7507789 < baseStart_7507789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507799 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_7507799 : Nat := 118140960795 + 7507799 * 2 ^ 59
def prefixEnd_7507799 : Nat := 4983230072969 + 3 ^ 40 * 7507799 * 2
def baseEnd_7507799 : Nat := 3855109544345176435584767

theorem tailTrace_7507799 : CollatzResearch.WordTrace tailWord_7507799 prefixEnd_7507799 3855109544345176435584767 := by
  unfold tailWord_7507799
  simp only [CollatzResearch.WordTrace]
  refine ⟨273831925727533927830766451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182554617151689285220510967 273831925727533927830766451)
  ·
    refine ⟨410747888591300891746149677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273831925727533927830766451 410747888591300891746149677)
    ·
      refine ⟨154030458221737834404806129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410747888591300891746149677 154030458221737834404806129)
      ·
        refine ⟨115522843666303375803604597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154030458221737834404806129 115522843666303375803604597)
        ·
          refine ⟨10830266593715941481587931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115522843666303375803604597 10830266593715941481587931)
          ·
            refine ⟨16245399890573912222381897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10830266593715941481587931 16245399890573912222381897)
            ·
              refine ⟨12184049917930434166786423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16245399890573912222381897 12184049917930434166786423)
              ·
                refine ⟨18276074876895651250179635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12184049917930434166786423 18276074876895651250179635)
                ·
                  refine ⟨27414112315343476875269453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18276074876895651250179635 27414112315343476875269453)
                  ·
                    refine ⟨10280292118253803828226045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27414112315343476875269453 10280292118253803828226045)
                    ·
                      refine ⟨3855109544345176435584767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10280292118253803828226045 3855109544345176435584767)
                      ·
                        rfl

theorem cell23_7507799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_7507799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507799 prefixEnd_7507799 := by exact prefixLift 7507799
  have htrace : WordTrace (prefixWord ++ tailWord_7507799) baseStart_7507799 baseEnd_7507799 := by
    simpa [prefixWord, tailWord_7507799, baseEnd_7507799] using wordTrace_append hprefix tailTrace_7507799
  have hstable : (prefixWord ++ tailWord_7507799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507799).length < 2 ^ (prefixWord ++ tailWord_7507799).sum := by decide
  have hdescent : baseEnd_7507799 < baseStart_7507799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507809 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_7507809 : Nat := 118140960795 + 7507809 * 2 ^ 59
def prefixEnd_7507809 : Nat := 4983230072969 + 3 ^ 40 * 7507809 * 2
def baseEnd_7507809 : Nat := 3855114679151721396459721

theorem tailTrace_7507809 : CollatzResearch.WordTrace tailWord_7507809 prefixEnd_7507809 3855114679151721396459721 := by
  unfold tailWord_7507809
  simp only [CollatzResearch.WordTrace]
  refine ⟨273832290457497699538630481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182554860304998466359086987 273832290457497699538630481)
  ·
    refine ⟨205374217843123274653972861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273832290457497699538630481 205374217843123274653972861)
    ·
      refine ⟨77015331691171227995239823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205374217843123274653972861 77015331691171227995239823)
      ·
        refine ⟨115522997536756841992859735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77015331691171227995239823 115522997536756841992859735)
        ·
          refine ⟨173284496305135262989289603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115522997536756841992859735 173284496305135262989289603)
          ·
            refine ⟨259926744457702894483934405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173284496305135262989289603 259926744457702894483934405)
            ·
              refine ⟨48736264585819292715737701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259926744457702894483934405 48736264585819292715737701)
              ·
                refine ⟨9138049609841117384200819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48736264585819292715737701 9138049609841117384200819)
                ·
                  refine ⟨13707074414761676076301229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9138049609841117384200819 13707074414761676076301229)
                  ·
                    refine ⟨5140152905535628528612961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13707074414761676076301229 5140152905535628528612961)
                    ·
                      refine ⟨3855114679151721396459721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140152905535628528612961 3855114679151721396459721)
                      ·
                        rfl

theorem cell23_7507809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_7507809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507809 prefixEnd_7507809 := by exact prefixLift 7507809
  have htrace : WordTrace (prefixWord ++ tailWord_7507809) baseStart_7507809 baseEnd_7507809 := by
    simpa [prefixWord, tailWord_7507809, baseEnd_7507809] using wordTrace_append hprefix tailTrace_7507809
  have hstable : (prefixWord ++ tailWord_7507809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507809).length < 2 ^ (prefixWord ++ tailWord_7507809).sum := by decide
  have hdescent : baseEnd_7507809 < baseStart_7507809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507815 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 1, 8]
def baseStart_7507815 : Nat := 118140960795 + 7507815 * 2 ^ 59
def prefixEnd_7507815 : Nat := 4983230072969 + 3 ^ 40 * 7507815 * 2
def baseEnd_7507815 : Nat := 1285039253345216124328231

theorem tailTrace_7507815 : CollatzResearch.WordTrace tailWord_7507815 prefixEnd_7507815 1285039253345216124328231 := by
  unfold tailWord_7507815
  simp only [CollatzResearch.WordTrace]
  refine ⟨273832509295475962563348899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182555006196983975042232599 273832509295475962563348899)
  ·
    refine ⟨410748763943213943845023349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273832509295475962563348899 410748763943213943845023349)
    ·
      refine ⟨38507696619676307235470939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 410748763943213943845023349 38507696619676307235470939)
      ·
        refine ⟨57761544929514460853206409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38507696619676307235470939 57761544929514460853206409)
        ·
          refine ⟨43321158697135845639904807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57761544929514460853206409 43321158697135845639904807)
          ·
            refine ⟨64981738045703768459857211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43321158697135845639904807 64981738045703768459857211)
            ·
              refine ⟨97472607068555652689785817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64981738045703768459857211 97472607068555652689785817)
              ·
                refine ⟨73104455301416739517339363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97472607068555652689785817 73104455301416739517339363)
                ·
                  refine ⟨109656682952125109276009045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73104455301416739517339363 109656682952125109276009045)
                  ·
                    refine ⟨1285039253345216124328231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109656682952125109276009045 1285039253345216124328231)
                    ·
                      rfl

theorem cell23_7507815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_7507815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507815 prefixEnd_7507815 := by exact prefixLift 7507815
  have htrace : WordTrace (prefixWord ++ tailWord_7507815) baseStart_7507815 baseEnd_7507815 := by
    simpa [prefixWord, tailWord_7507815, baseEnd_7507815] using wordTrace_append hprefix tailTrace_7507815
  have hstable : (prefixWord ++ tailWord_7507815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507815).length < 2 ^ (prefixWord ++ tailWord_7507815).sum := by decide
  have hdescent : baseEnd_7507815 < baseStart_7507815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507825 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_7507825 : Nat := 118140960795 + 7507825 * 2 ^ 59
def prefixEnd_7507825 : Nat := 4983230072969 + 3 ^ 40 * 7507825 * 2
def baseEnd_7507825 : Nat := 3855122894842193333859647

theorem tailTrace_7507825 : CollatzResearch.WordTrace tailWord_7507825 prefixEnd_7507825 3855122894842193333859647 := by
  unfold tailWord_7507825
  simp only [CollatzResearch.WordTrace]
  refine ⟨273832874025439734271212929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182555249350293156180808619 273832874025439734271212929)
  ·
    refine ⟨205374655519079800703409697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273832874025439734271212929 205374655519079800703409697)
    ·
      refine ⟨154030991639309850527557273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205374655519079800703409697 154030991639309850527557273)
      ·
        refine ⟨115523243729482387895667955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154030991639309850527557273 115523243729482387895667955)
        ·
          refine ⟨173284865594223581843501933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115523243729482387895667955 173284865594223581843501933)
          ·
            refine ⟨64981824597833843191313225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173284865594223581843501933 64981824597833843191313225)
            ·
              refine ⟨48736368448375382393484919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64981824597833843191313225 48736368448375382393484919)
              ·
                refine ⟨73104552672563073590227379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48736368448375382393484919 73104552672563073590227379)
                ·
                  refine ⟨109656829008844610385341069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73104552672563073590227379 109656829008844610385341069)
                  ·
                    refine ⟨41121310878316728894502901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109656829008844610385341069 41121310878316728894502901)
                    ·
                      refine ⟨3855122894842193333859647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41121310878316728894502901 3855122894842193333859647)
                      ·
                        rfl

theorem cell23_7507825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_7507825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507825 prefixEnd_7507825 := by exact prefixLift 7507825
  have htrace : WordTrace (prefixWord ++ tailWord_7507825) baseStart_7507825 baseEnd_7507825 := by
    simpa [prefixWord, tailWord_7507825, baseEnd_7507825] using wordTrace_append hprefix tailTrace_7507825
  have hstable : (prefixWord ++ tailWord_7507825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507825).length < 2 ^ (prefixWord ++ tailWord_7507825).sum := by decide
  have hdescent : baseEnd_7507825 < baseStart_7507825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507902 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_7507902 : Nat := 118140960795 + 7507902 * 2 ^ 59
def prefixEnd_7507902 : Nat := 4983230072969 + 3 ^ 40 * 7507902 * 2
def baseEnd_7507902 : Nat := 3855162432852589532596793

theorem tailTrace_7507902 : CollatzResearch.WordTrace tailWord_7507902 prefixEnd_7507902 3855162432852589532596793 := by
  unfold tailWord_7507902
  simp only [CollatzResearch.WordTrace]
  refine ⟨34229460305770097052720745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182557121630773850947843973 34229460305770097052720745)
  ·
    refine ⟨25672095229327572789540559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34229460305770097052720745 25672095229327572789540559)
    ·
      refine ⟨38508142843991359184310839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25672095229327572789540559 38508142843991359184310839)
      ·
        refine ⟨57762214265987038776466259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38508142843991359184310839 57762214265987038776466259)
        ·
          refine ⟨86643321398980558164699389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57762214265987038776466259 86643321398980558164699389)
          ·
            refine ⟨32491245524617709311762271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86643321398980558164699389 32491245524617709311762271)
            ·
              refine ⟨48736868286926563967643407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32491245524617709311762271 48736868286926563967643407)
              ·
                refine ⟨73105302430389845951465111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48736868286926563967643407 73105302430389845951465111)
                ·
                  refine ⟨109657953645584768927197667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73105302430389845951465111 109657953645584768927197667)
                  ·
                    refine ⟨164486930468377153390796501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109657953645584768927197667 164486930468377153390796501)
                    ·
                      refine ⟨3855162432852589532596793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164486930468377153390796501 3855162432852589532596793)
                      ·
                        rfl

theorem cell23_7507902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_7507902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507902 prefixEnd_7507902 := by exact prefixLift 7507902
  have htrace : WordTrace (prefixWord ++ tailWord_7507902) baseStart_7507902 baseEnd_7507902 := by
    simpa [prefixWord, tailWord_7507902, baseEnd_7507902] using wordTrace_append hprefix tailTrace_7507902
  have hstable : (prefixWord ++ tailWord_7507902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507902).length < 2 ^ (prefixWord ++ tailWord_7507902).sum := by decide
  have hdescent : baseEnd_7507902 < baseStart_7507902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507952 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 6]
def baseStart_7507952 : Nat := 118140960795 + 7507952 * 2 ^ 59
def prefixEnd_7507952 : Nat := 4983230072969 + 3 ^ 40 * 7507952 * 2
def baseEnd_7507952 : Nat := 428354234098368259663507

theorem tailTrace_7507952 : CollatzResearch.WordTrace tailWord_7507952 prefixEnd_7507952 428354234098368259663507 := by
  unfold tailWord_7507952
  simp only [CollatzResearch.WordTrace]
  refine ⟨136918753047989817480543055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182558337397319756640724073 136918753047989817480543055)
  ·
    refine ⟨205378129571984726220814583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136918753047989817480543055 205378129571984726220814583)
    ·
      refine ⟨308067194357977089331221875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205378129571984726220814583 308067194357977089331221875)
      ·
        refine ⟨462100791536965633996832813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308067194357977089331221875 462100791536965633996832813)
        ·
          refine ⟨173287796826362112748812305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462100791536965633996832813 173287796826362112748812305)
          ·
            refine ⟨129965847619771584561609229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173287796826362112748812305 129965847619771584561609229)
            ·
              refine ⟨48737192857414344210603461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129965847619771584561609229 48737192857414344210603461)
              ·
                refine ⟨9138223660765189539488149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48737192857414344210603461 9138223660765189539488149)
                ·
                  refine ⟨428354234098368259663507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9138223660765189539488149 428354234098368259663507)
                  ·
                    rfl

theorem cell23_7507952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 6].length) (baseStart_7507952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507952 prefixEnd_7507952 := by exact prefixLift 7507952
  have htrace : WordTrace (prefixWord ++ tailWord_7507952) baseStart_7507952 baseEnd_7507952 := by
    simpa [prefixWord, tailWord_7507952, baseEnd_7507952] using wordTrace_append hprefix tailTrace_7507952
  have hstable : (prefixWord ++ tailWord_7507952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507952).length < 2 ^ (prefixWord ++ tailWord_7507952).sum := by decide
  have hdescent : baseEnd_7507952 < baseStart_7507952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507962 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_7507962 : Nat := 118140960795 + 7507962 * 2 ^ 59
def prefixEnd_7507962 : Nat := 4983230072969 + 3 ^ 40 * 7507962 * 2
def baseEnd_7507962 : Nat := 3855193241691859297846517

theorem tailTrace_7507962 : CollatzResearch.WordTrace tailWord_7507962 prefixEnd_7507962 3855193241691859297846517 := by
  unfold tailWord_7507962
  simp only [CollatzResearch.WordTrace]
  refine ⟨68459467706485851667237535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182558580550628937779300093 68459467706485851667237535)
  ·
    refine ⟨102689201559728777500856303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68459467706485851667237535 102689201559728777500856303)
    ·
      refine ⟨154033802339593166251284455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102689201559728777500856303 154033802339593166251284455)
      ·
        refine ⟨231050703509389749376926683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154033802339593166251284455 231050703509389749376926683)
        ·
          refine ⟨346576055264084624065390025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231050703509389749376926683 346576055264084624065390025)
          ·
            refine ⟨259932041448063468049042519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346576055264084624065390025 259932041448063468049042519)
            ·
              refine ⟨389898062172095202073563779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259932041448063468049042519 389898062172095202073563779)
              ·
                refine ⟨584847093258142803110345669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389898062172095202073563779 584847093258142803110345669)
                ·
                  refine ⟨109658829985901775583189813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 584847093258142803110345669 109658829985901775583189813)
                  ·
                    refine ⟨10280515311178291460924045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109658829985901775583189813 10280515311178291460924045)
                    ·
                      refine ⟨3855193241691859297846517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10280515311178291460924045 3855193241691859297846517)
                      ·
                        rfl

theorem cell23_7507962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_7507962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507962 prefixEnd_7507962 := by exact prefixLift 7507962
  have htrace : WordTrace (prefixWord ++ tailWord_7507962) baseStart_7507962 baseEnd_7507962 := by
    simpa [prefixWord, tailWord_7507962, baseEnd_7507962] using wordTrace_append hprefix tailTrace_7507962
  have hstable : (prefixWord ++ tailWord_7507962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507962).length < 2 ^ (prefixWord ++ tailWord_7507962).sum := by decide
  have hdescent : baseEnd_7507962 < baseStart_7507962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7507999 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 1, 5]
def baseStart_7507999 : Nat := 118140960795 + 7507999 * 2 ^ 59
def prefixEnd_7507999 : Nat := 4983230072969 + 3 ^ 40 * 7507999 * 2
def baseEnd_7507999 : Nat := 1285070746825358551027949

theorem tailTrace_7507999 : CollatzResearch.WordTrace tailWord_7507999 prefixEnd_7507999 1285070746825358551027949 := by
  unfold tailWord_7507999
  simp only [CollatzResearch.WordTrace]
  refine ⟨273839220326809361988047051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182559480217872907992031367 273839220326809361988047051)
  ·
    refine ⟨410758830490214042982070577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273839220326809361988047051 410758830490214042982070577)
    ·
      refine ⟨308069122867660532236552933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410758830490214042982070577 308069122867660532236552933)
      ·
        refine ⟨57762960537686349794353675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308069122867660532236552933 57762960537686349794353675)
        ·
          refine ⟨86644440806529524691530513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57762960537686349794353675 86644440806529524691530513)
          ·
            refine ⟨64983330604897143518647885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86644440806529524691530513 64983330604897143518647885)
            ·
              refine ⟨24368748976836428819492957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64983330604897143518647885 24368748976836428819492957)
              ·
                refine ⟨9138280866313660807309859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24368748976836428819492957 9138280866313660807309859)
                ·
                  refine ⟨13707421299470491210964789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9138280866313660807309859 13707421299470491210964789)
                  ·
                    refine ⟨1285070746825358551027949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13707421299470491210964789 1285070746825358551027949)
                    ·
                      rfl

theorem cell23_7507999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 5].length) (baseStart_7507999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7507999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7507999 prefixEnd_7507999 := by exact prefixLift 7507999
  have htrace : WordTrace (prefixWord ++ tailWord_7507999) baseStart_7507999 baseEnd_7507999 := by
    simpa [prefixWord, tailWord_7507999, baseEnd_7507999] using wordTrace_append hprefix tailTrace_7507999
  have hstable : (prefixWord ++ tailWord_7507999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7507999).length < 2 ^ (prefixWord ++ tailWord_7507999).sum := by decide
  have hdescent : baseEnd_7507999 < baseStart_7507999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7507999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508056 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 1, 2, 3]
def baseStart_7508056 : Nat := 118140960795 + 7508056 * 2 ^ 59
def prefixEnd_7508056 : Nat := 4983230072969 + 3 ^ 40 * 7508056 * 2
def baseEnd_7508056 : Nat := 3855241508873381930071085

theorem tailTrace_7508056 : CollatzResearch.WordTrace tailWord_7508056 prefixEnd_7508056 3855241508873381930071085 := by
  unfold tailWord_7508056
  simp only [CollatzResearch.WordTrace]
  refine ⟨136920649643801430361436011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182560866191735240481914681 136920649643801430361436011)
  ·
    refine ⟨205380974465702145542154017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136920649643801430361436011 205380974465702145542154017)
    ·
      refine ⟨154035730849276609156615513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205380974465702145542154017 154035730849276609156615513)
      ·
        refine ⟨115526798136957456867461635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154035730849276609156615513 115526798136957456867461635)
        ·
          refine ⟨173290197205436185301192453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115526798136957456867461635 173290197205436185301192453)
          ·
            refine ⟨32491911976019284743973585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173290197205436185301192453 32491911976019284743973585)
            ·
              refine ⟨24368933982014463557980189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32491911976019284743973585 24368933982014463557980189)
              ·
                refine ⟨9138350243255423834242571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24368933982014463557980189 9138350243255423834242571)
                ·
                  refine ⟨13707525364883135751363857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9138350243255423834242571 13707525364883135751363857)
                  ·
                    refine ⟨10280644023662351813522893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13707525364883135751363857 10280644023662351813522893)
                    ·
                      refine ⟨3855241508873381930071085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10280644023662351813522893 3855241508873381930071085)
                      ·
                        rfl

theorem cell23_7508056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_7508056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508056 prefixEnd_7508056 := by exact prefixLift 7508056
  have htrace : WordTrace (prefixWord ++ tailWord_7508056) baseStart_7508056 baseEnd_7508056 := by
    simpa [prefixWord, tailWord_7508056, baseEnd_7508056] using wordTrace_append hprefix tailTrace_7508056
  have hstable : (prefixWord ++ tailWord_7508056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508056).length < 2 ^ (prefixWord ++ tailWord_7508056).sum := by decide
  have hdescent : baseEnd_7508056 < baseStart_7508056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508120 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 2, 1, 3]
def baseStart_7508120 : Nat := 118140960795 + 7508120 * 2 ^ 59
def prefixEnd_7508120 : Nat := 4983230072969 + 3 ^ 40 * 7508120 * 2
def baseEnd_7508120 : Nat := 3855274371635269679670791

theorem tailTrace_7508120 : CollatzResearch.WordTrace tailWord_7508120 prefixEnd_7508120 3855274371635269679670791 := by
  unfold tailWord_7508120
  simp only [CollatzResearch.WordTrace]
  refine ⟨136921816779685499826600907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182562422372913999768801209 136921816779685499826600907)
  ·
    refine ⟨205382725169528249739901361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136921816779685499826600907 205382725169528249739901361)
    ·
      refine ⟨154037043877146187304926021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205382725169528249739901361 154037043877146187304926021)
      ·
        refine ⟨28881945726964910119673629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154037043877146187304926021 28881945726964910119673629)
        ·
          refine ⟨10830729647611841294877611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28881945726964910119673629 10830729647611841294877611)
          ·
            refine ⟨16246094471417761942316417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10830729647611841294877611 16246094471417761942316417)
            ·
              refine ⟨12184570853563321456737313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16246094471417761942316417 12184570853563321456737313)
              ·
                refine ⟨9138428140172491092552985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12184570853563321456737313 9138428140172491092552985)
                ·
                  refine ⟨6853821105129368319414739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9138428140172491092552985 6853821105129368319414739)
                  ·
                    refine ⟨10280731657694052479122109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6853821105129368319414739 10280731657694052479122109)
                    ·
                      refine ⟨3855274371635269679670791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10280731657694052479122109 3855274371635269679670791)
                      ·
                        rfl

theorem cell23_7508120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_7508120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508120 prefixEnd_7508120 := by exact prefixLift 7508120
  have htrace : WordTrace (prefixWord ++ tailWord_7508120) baseStart_7508120 baseEnd_7508120 := by
    simpa [prefixWord, tailWord_7508120, baseEnd_7508120] using wordTrace_append hprefix tailTrace_7508120
  have hstable : (prefixWord ++ tailWord_7508120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508120).length < 2 ^ (prefixWord ++ tailWord_7508120).sum := by decide
  have hdescent : baseEnd_7508120 < baseStart_7508120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508159 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 3]
def baseStart_7508159 : Nat := 118140960795 + 7508159 * 2 ^ 59
def prefixEnd_7508159 : Nat := 4983230072969 + 3 ^ 40 * 7508159 * 2
def baseEnd_7508159 : Nat := 3855294397380795027083111

theorem tailTrace_7508159 : CollatzResearch.WordTrace tailWord_7508159 prefixEnd_7508159 3855294397380795027083111 := by
  unfold tailWord_7508159
  simp only [CollatzResearch.WordTrace]
  refine ⟨273845056006229709313871531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182563370670819806209247687 273845056006229709313871531)
  ·
    refine ⟨410767584009344563970807297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273845056006229709313871531 410767584009344563970807297)
    ·
      refine ⟨308075688007008422978105473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410767584009344563970807297 308075688007008422978105473)
      ·
        refine ⟨231056766005256317233579105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308075688007008422978105473 231056766005256317233579105)
        ·
          refine ⟨173292574503942237925184329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231056766005256317233579105 173292574503942237925184329)
          ·
            refine ⟨129969430877956678443888247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173292574503942237925184329 129969430877956678443888247)
            ·
              refine ⟨194954146316935017665832371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129969430877956678443888247 194954146316935017665832371)
              ·
                refine ⟨292431219475402526498748557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194954146316935017665832371 292431219475402526498748557)
                ·
                  refine ⟨109661707303275947437030709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292431219475402526498748557 109661707303275947437030709)
                  ·
                    refine ⟨10280785059682120072221629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109661707303275947437030709 10280785059682120072221629)
                    ·
                      refine ⟨3855294397380795027083111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10280785059682120072221629 3855294397380795027083111)
                      ·
                        rfl

theorem cell23_7508159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_7508159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508159 prefixEnd_7508159 := by exact prefixLift 7508159
  have htrace : WordTrace (prefixWord ++ tailWord_7508159) baseStart_7508159 baseEnd_7508159 := by
    simpa [prefixWord, tailWord_7508159, baseEnd_7508159] using wordTrace_append hprefix tailTrace_7508159
  have hstable : (prefixWord ++ tailWord_7508159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508159).length < 2 ^ (prefixWord ++ tailWord_7508159).sum := by decide
  have hdescent : baseEnd_7508159 < baseStart_7508159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508186 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2]
def baseStart_7508186 : Nat := 118140960795 + 7508186 * 2 ^ 59
def prefixEnd_7508186 : Nat := 4983230072969 + 3 ^ 40 * 7508186 * 2
def baseEnd_7508186 : Nat := 3855308261358466421445487

theorem tailTrace_7508186 : CollatzResearch.WordTrace tailWord_7508186 prefixEnd_7508186 3855308261358466421445487 := by
  unfold tailWord_7508186
  simp only [CollatzResearch.WordTrace]
  refine ⟨68461510194282973231276103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182564027184754595283402941 68461510194282973231276103)
  ·
    refine ⟨102692265291424459846914155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68461510194282973231276103 102692265291424459846914155)
    ·
      refine ⟨154038397937136689770371233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102692265291424459846914155 154038397937136689770371233)
      ·
        refine ⟨115528798452852517327778425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154038397937136689770371233 115528798452852517327778425)
        ·
          refine ⟨86646598839639387995833819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115528798452852517327778425 86646598839639387995833819)
          ·
            refine ⟨129969898259459081993750729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86646598839639387995833819 129969898259459081993750729)
            ·
              refine ⟨97477423694594311495313047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129969898259459081993750729 97477423694594311495313047)
              ·
                refine ⟨146216135541891467242969571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97477423694594311495313047 146216135541891467242969571)
                ·
                  refine ⟨219324203312837200864454357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146216135541891467242969571 219324203312837200864454357)
                  ·
                    refine ⟨5140411015144621895260649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 219324203312837200864454357 5140411015144621895260649)
                    ·
                      refine ⟨3855308261358466421445487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140411015144621895260649 3855308261358466421445487)
                      ·
                        rfl

theorem cell23_7508186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_7508186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508186 prefixEnd_7508186 := by exact prefixLift 7508186
  have htrace : WordTrace (prefixWord ++ tailWord_7508186) baseStart_7508186 baseEnd_7508186 := by
    simpa [prefixWord, tailWord_7508186, baseEnd_7508186] using wordTrace_append hprefix tailTrace_7508186
  have hstable : (prefixWord ++ tailWord_7508186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508186).length < 2 ^ (prefixWord ++ tailWord_7508186).sum := by decide
  have hdescent : baseEnd_7508186 < baseStart_7508186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508216 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 1, 6, 2]
def baseStart_7508216 : Nat := 118140960795 + 7508216 * 2 ^ 59
def prefixEnd_7508216 : Nat := 4983230072969 + 3 ^ 40 * 7508216 * 2
def baseEnd_7508216 : Nat := 3855323665778101304070349

theorem tailTrace_7508216 : CollatzResearch.WordTrace tailWord_7508216 prefixEnd_7508216 3855323665778101304070349 := by
  unfold tailWord_7508216
  simp only [CollatzResearch.WordTrace]
  refine ⟨136923567483511604024348251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182564756644682138699131001 136923567483511604024348251)
  ·
    refine ⟨205385351225267406036522377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136923567483511604024348251 205385351225267406036522377)
    ·
      refine ⟨154039013418950554527391783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205385351225267406036522377 154039013418950554527391783)
      ·
        refine ⟨231058520128425831791087675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154039013418950554527391783 231058520128425831791087675)
        ·
          refine ⟨346587780192638747686631513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231058520128425831791087675 346587780192638747686631513)
          ·
            refine ⟨259940835144479060764973635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346587780192638747686631513 259940835144479060764973635)
            ·
              refine ⟨389911252716718591147460453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259940835144479060764973635 389911252716718591147460453)
              ·
                refine ⟨73108359884384735840148835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389911252716718591147460453 73108359884384735840148835)
                ·
                  refine ⟨109662539826577103760223253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73108359884384735840148835 109662539826577103760223253)
                  ·
                    refine ⟨5140431554370801738760465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109662539826577103760223253 5140431554370801738760465)
                    ·
                      refine ⟨3855323665778101304070349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140431554370801738760465 3855323665778101304070349)
                      ·
                        rfl

theorem cell23_7508216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_7508216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508216 prefixEnd_7508216 := by exact prefixLift 7508216
  have htrace : WordTrace (prefixWord ++ tailWord_7508216) baseStart_7508216 baseEnd_7508216 := by
    simpa [prefixWord, tailWord_7508216, baseEnd_7508216] using wordTrace_append hprefix tailTrace_7508216
  have hstable : (prefixWord ++ tailWord_7508216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508216).length < 2 ^ (prefixWord ++ tailWord_7508216).sum := by decide
  have hdescent : baseEnd_7508216 < baseStart_7508216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508229 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 6]
def baseStart_7508229 : Nat := 118140960795 + 7508229 * 2 ^ 59
def prefixEnd_7508229 : Nat := 4983230072969 + 3 ^ 40 * 7508229 * 2
def baseEnd_7508229 : Nat := 3855330341026609753207789

theorem tailTrace_7508229 : CollatzResearch.WordTrace tailWord_7508229 prefixEnd_7508229 3855330341026609753207789 := by
  unfold tailWord_7508229
  simp only [CollatzResearch.WordTrace]
  refine ⟨273847609115976111268919741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182565072743984074179279827 273847609115976111268919741)
  ·
    refine ⟨102692853418491041725844903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273847609115976111268919741 102692853418491041725844903)
    ·
      refine ⟨154039280127736562588767355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102692853418491041725844903 154039280127736562588767355)
      ·
        refine ⟨231058920191604843883151033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154039280127736562588767355 231058920191604843883151033)
        ·
          refine ⟨173294190143703632912363275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231058920191604843883151033 173294190143703632912363275)
          ·
            refine ⟨259941285215555449368544913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173294190143703632912363275 259941285215555449368544913)
            ·
              refine ⟨194955963911666587026408685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259941285215555449368544913 194955963911666587026408685)
              ·
                refine ⟨73108486466874970134903257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194955963911666587026408685 73108486466874970134903257)
                ·
                  refine ⟨54831364850156227601177443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73108486466874970134903257 54831364850156227601177443)
                  ·
                    refine ⟨82247047275234341401766165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54831364850156227601177443 82247047275234341401766165)
                    ·
                      refine ⟨3855330341026609753207789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82247047275234341401766165 3855330341026609753207789)
                      ·
                        rfl

theorem cell23_7508229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_7508229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508229 prefixEnd_7508229 := by exact prefixLift 7508229
  have htrace : WordTrace (prefixWord ++ tailWord_7508229) baseStart_7508229 baseEnd_7508229 := by
    simpa [prefixWord, tailWord_7508229, baseEnd_7508229] using wordTrace_append hprefix tailTrace_7508229
  have hstable : (prefixWord ++ tailWord_7508229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508229).length < 2 ^ (prefixWord ++ tailWord_7508229).sum := by decide
  have hdescent : baseEnd_7508229 < baseStart_7508229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508243 : List Nat := [1, 1, 1, 2, 1, 3, 1, 8, 1, 4]
def baseStart_7508243 : Nat := 118140960795 + 7508243 * 2 ^ 59
def prefixEnd_7508243 : Nat := 4983230072969 + 3 ^ 40 * 7508243 * 2
def baseEnd_7508243 : Nat := 1285112509918590899477575

theorem tailTrace_7508243 : CollatzResearch.WordTrace tailWord_7508243 prefixEnd_7508243 1285112509918590899477575 := by
  unfold tailWord_7508243
  simp only [CollatzResearch.WordTrace]
  refine ⟨273848119737925391659929383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182565413158616927773286255 273848119737925391659929383)
  ·
    refine ⟨410772179606888087489894075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273848119737925391659929383 410772179606888087489894075)
    ·
      refine ⟨616158269410332131234841113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410772179606888087489894075 616158269410332131234841113)
      ·
        refine ⟨462118702057749098426130835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616158269410332131234841113 462118702057749098426130835)
        ·
          refine ⟨693178053086623647639196253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462118702057749098426130835 693178053086623647639196253)
          ·
            refine ⟨259941769907483867864698595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 693178053086623647639196253 259941769907483867864698595)
            ·
              refine ⟨389912654861225801797047893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259941769907483867864698595 389912654861225801797047893)
              ·
                refine ⟨4569288924154989864809155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 389912654861225801797047893 4569288924154989864809155)
                ·
                  refine ⟨6853933386232484797213733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569288924154989864809155 6853933386232484797213733)
                  ·
                    refine ⟨1285112509918590899477575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6853933386232484797213733 1285112509918590899477575)
                    ·
                      rfl

theorem cell23_7508243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 4].length) (baseStart_7508243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508243 prefixEnd_7508243 := by exact prefixLift 7508243
  have htrace : WordTrace (prefixWord ++ tailWord_7508243) baseStart_7508243 baseEnd_7508243 := by
    simpa [prefixWord, tailWord_7508243, baseEnd_7508243] using wordTrace_append hprefix tailTrace_7508243
  have hstable : (prefixWord ++ tailWord_7508243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508243).length < 2 ^ (prefixWord ++ tailWord_7508243).sum := by decide
  have hdescent : baseEnd_7508243 < baseStart_7508243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508279 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_7508279 : Nat := 118140960795 + 7508279 * 2 ^ 59
def prefixEnd_7508279 : Nat := 4983230072969 + 3 ^ 40 * 7508279 * 2
def baseEnd_7508279 : Nat := 3855356015059334557582559

theorem tailTrace_7508279 : CollatzResearch.WordTrace tailWord_7508279 prefixEnd_7508279 3855356015059334557582559 := by
  unfold tailWord_7508279
  simp only [CollatzResearch.WordTrace]
  refine ⟨273849432765794969808239891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182566288510529979872159927 273849432765794969808239891)
  ·
    refine ⟨410774149148692454712359837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273849432765794969808239891 410774149148692454712359837)
    ·
      refine ⟨154040305930759670517134939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410774149148692454712359837 154040305930759670517134939)
      ·
        refine ⟨231060458896139505775702409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154040305930759670517134939 231060458896139505775702409)
        ·
          refine ⟨173295344172104629331776807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231060458896139505775702409 173295344172104629331776807)
          ·
            refine ⟨259943016258156943997665211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173295344172104629331776807 259943016258156943997665211)
            ·
              refine ⟨389914524387235415996497817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259943016258156943997665211 389914524387235415996497817)
              ·
                refine ⟨292435893290426561997373363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389914524387235415996497817 292435893290426561997373363)
                ·
                  refine ⟨438653839935639842996060045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292435893290426561997373363 438653839935639842996060045)
                  ·
                    refine ⟨164495189975864941123522517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 438653839935639842996060045 164495189975864941123522517)
                    ·
                      refine ⟨3855356015059334557582559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164495189975864941123522517 3855356015059334557582559)
                      ·
                        rfl

theorem cell23_7508279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_7508279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508279 prefixEnd_7508279 := by exact prefixLift 7508279
  have htrace : WordTrace (prefixWord ++ tailWord_7508279) baseStart_7508279 baseEnd_7508279 := by
    simpa [prefixWord, tailWord_7508279, baseEnd_7508279] using wordTrace_append hprefix tailTrace_7508279
  have hstable : (prefixWord ++ tailWord_7508279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508279).length < 2 ^ (prefixWord ++ tailWord_7508279).sum := by decide
  have hdescent : baseEnd_7508279 < baseStart_7508279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508318 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_7508318 : Nat := 118140960795 + 7508318 * 2 ^ 59
def prefixEnd_7508318 : Nat := 4983230072969 + 3 ^ 40 * 7508318 * 2
def baseEnd_7508318 : Nat := 3855376040804859904994881

theorem tailTrace_7508318 : CollatzResearch.WordTrace tailWord_7508318 prefixEnd_7508318 3855376040804859904994881 := by
  unfold tailWord_7508318
  simp only [CollatzResearch.WordTrace]
  refine ⟨34231356901581709933613701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182567236808435786312606405 34231356901581709933613701)
  ·
    refine ⟨6418379419046570612552569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34231356901581709933613701 6418379419046570612552569)
    ·
      refine ⟨4813784564284927959414427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6418379419046570612552569 4813784564284927959414427)
      ·
        refine ⟨7220676846427391939121641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4813784564284927959414427 7220676846427391939121641)
        ·
          refine ⟨5415507634820543954341231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7220676846427391939121641 5415507634820543954341231)
          ·
            refine ⟨8123261452230815931511847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415507634820543954341231 8123261452230815931511847)
            ·
              refine ⟨12184892178346223897267771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123261452230815931511847 12184892178346223897267771)
              ·
                refine ⟨18277338267519335845901657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12184892178346223897267771 18277338267519335845901657)
                ·
                  refine ⟨13708003700639501884426243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18277338267519335845901657 13708003700639501884426243)
                  ·
                    refine ⟨20562005550959252826639365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13708003700639501884426243 20562005550959252826639365)
                    ·
                      refine ⟨3855376040804859904994881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20562005550959252826639365 3855376040804859904994881)
                      ·
                        rfl

theorem cell23_7508318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_7508318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508318 prefixEnd_7508318 := by exact prefixLift 7508318
  have htrace : WordTrace (prefixWord ++ tailWord_7508318) baseStart_7508318 baseEnd_7508318 := by
    simpa [prefixWord, tailWord_7508318, baseEnd_7508318] using wordTrace_append hprefix tailTrace_7508318
  have hstable : (prefixWord ++ tailWord_7508318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508318).length < 2 ^ (prefixWord ++ tailWord_7508318).sum := by decide
  have hdescent : baseEnd_7508318 < baseStart_7508318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508323 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 4]
def baseStart_7508323 : Nat := 118140960795 + 7508323 * 2 ^ 59
def prefixEnd_7508323 : Nat := 4983230072969 + 3 ^ 40 * 7508323 * 2
def baseEnd_7508323 : Nat := 3855378608208132385432357

theorem tailTrace_7508323 : CollatzResearch.WordTrace tailWord_7508323 prefixEnd_7508323 3855378608208132385432357 := by
  unfold tailWord_7508323
  simp only [CollatzResearch.WordTrace]
  refine ⟨273851037577635565322841623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182567358385090376881894415 273851037577635565322841623)
  ·
    refine ⟨410776556366453347984262435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273851037577635565322841623 410776556366453347984262435)
    ·
      refine ⟨616164834549680021976393653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410776556366453347984262435 616164834549680021976393653)
      ·
        refine ⟨57765453239032502060286905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 616164834549680021976393653 57765453239032502060286905)
        ·
          refine ⟨43324089929274376545215179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57765453239032502060286905 43324089929274376545215179)
          ·
            refine ⟨64986134893911564817822769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43324089929274376545215179 64986134893911564817822769)
            ·
              refine ⟨48739601170433673613367077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64986134893911564817822769 48739601170433673613367077)
              ·
                refine ⟨9138675219456313802506327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48739601170433673613367077 9138675219456313802506327)
                ·
                  refine ⟨13708012829184470703759491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9138675219456313802506327 13708012829184470703759491)
                  ·
                    refine ⟨20562019243776706055639237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13708012829184470703759491 20562019243776706055639237)
                    ·
                      refine ⟨3855378608208132385432357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20562019243776706055639237 3855378608208132385432357)
                      ·
                        rfl

theorem cell23_7508323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_7508323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508323 prefixEnd_7508323 := by exact prefixLift 7508323
  have htrace : WordTrace (prefixWord ++ tailWord_7508323) baseStart_7508323 baseEnd_7508323 := by
    simpa [prefixWord, tailWord_7508323, baseEnd_7508323] using wordTrace_append hprefix tailTrace_7508323
  have hstable : (prefixWord ++ tailWord_7508323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508323).length < 2 ^ (prefixWord ++ tailWord_7508323).sum := by decide
  have hdescent : baseEnd_7508323 < baseStart_7508323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508327 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_7508327 : Nat := 118140960795 + 7508327 * 2 ^ 59
def prefixEnd_7508327 : Nat := 4983230072969 + 3 ^ 40 * 7508327 * 2
def baseEnd_7508327 : Nat := 3855380662130750369782339

theorem tailTrace_7508327 : CollatzResearch.WordTrace tailWord_7508327 prefixEnd_7508327 3855380662130750369782339 := by
  unfold tailWord_7508327
  simp only [CollatzResearch.WordTrace]
  refine ⟨273851183469621074005987235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182567455646414049337324823 273851183469621074005987235)
  ·
    refine ⟨410776775204431611008980853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273851183469621074005987235 410776775204431611008980853)
    ·
      refine ⟨38510322675415463532091955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 410776775204431611008980853 38510322675415463532091955)
      ·
        refine ⟨57765484013123195298137933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38510322675415463532091955 57765484013123195298137933)
        ·
          refine ⟨21662056504921198236801725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57765484013123195298137933 21662056504921198236801725)
          ·
            refine ⟨8123271189345449338800647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21662056504921198236801725 8123271189345449338800647)
            ·
              refine ⟨12184906784018174008200971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123271189345449338800647 12184906784018174008200971)
              ·
                refine ⟨18277360176027261012301457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12184906784018174008200971 18277360176027261012301457)
                ·
                  refine ⟨13708020132020445759226093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18277360176027261012301457 13708020132020445759226093)
                  ·
                    refine ⟨5140507549507667159709785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13708020132020445759226093 5140507549507667159709785)
                    ·
                      refine ⟨3855380662130750369782339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140507549507667159709785 3855380662130750369782339)
                      ·
                        rfl

theorem cell23_7508327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_7508327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508327 prefixEnd_7508327 := by exact prefixLift 7508327
  have htrace : WordTrace (prefixWord ++ tailWord_7508327) baseStart_7508327 baseEnd_7508327 := by
    simpa [prefixWord, tailWord_7508327, baseEnd_7508327] using wordTrace_append hprefix tailTrace_7508327
  have hstable : (prefixWord ++ tailWord_7508327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508327).length < 2 ^ (prefixWord ++ tailWord_7508327).sum := by decide
  have hdescent : baseEnd_7508327 < baseStart_7508327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508333 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_7508333 : Nat := 118140960795 + 7508333 * 2 ^ 59
def prefixEnd_7508333 : Nat := 4983230072969 + 3 ^ 40 * 7508333 * 2
def baseEnd_7508333 : Nat := 1285127914338225782102437

theorem tailTrace_7508333 : CollatzResearch.WordTrace tailWord_7508333 prefixEnd_7508333 1285127914338225782102437 := by
  unfold tailWord_7508333
  simp only [CollatzResearch.WordTrace]
  refine ⟨273851402307599337030705653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182567601538399558020470435 273851402307599337030705653)
  ·
    refine ⟨25673568966337437846628655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273851402307599337030705653 25673568966337437846628655)
    ·
      refine ⟨38510353449506156769942983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25673568966337437846628655 38510353449506156769942983)
      ·
        refine ⟨57765530174259235154914475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38510353449506156769942983 57765530174259235154914475)
        ·
          refine ⟨86648295261388852732371713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57765530174259235154914475 86648295261388852732371713)
          ·
            refine ⟨64986221446041639549278785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86648295261388852732371713 64986221446041639549278785)
            ·
              refine ⟨48739666084531229661959089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64986221446041639549278785 48739666084531229661959089)
              ·
                refine ⟨36554749563398422246469317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48739666084531229661959089 36554749563398422246469317)
                ·
                  refine ⟨6854015543137204171212997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36554749563398422246469317 6854015543137204171212997)
                  ·
                    refine ⟨1285127914338225782102437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854015543137204171212997 1285127914338225782102437)
                    ·
                      rfl

theorem cell23_7508333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_7508333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508333 prefixEnd_7508333 := by exact prefixLift 7508333
  have htrace : WordTrace (prefixWord ++ tailWord_7508333) baseStart_7508333 baseEnd_7508333 := by
    simpa [prefixWord, tailWord_7508333, baseEnd_7508333] using wordTrace_append hprefix tailTrace_7508333
  have hstable : (prefixWord ++ tailWord_7508333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508333).length < 2 ^ (prefixWord ++ tailWord_7508333).sum := by decide
  have hdescent : baseEnd_7508333 < baseStart_7508333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508391 : List Nat := [1, 1, 6, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_7508391 : Nat := 118140960795 + 7508391 * 2 ^ 59
def prefixEnd_7508391 : Nat := 4983230072969 + 3 ^ 40 * 7508391 * 2
def baseEnd_7508391 : Nat := 3855413524892638119382045

theorem tailTrace_7508391 : CollatzResearch.WordTrace tailWord_7508391 prefixEnd_7508391 3855413524892638119382045 := by
  unfold tailWord_7508391
  simp only [CollatzResearch.WordTrace]
  refine ⟨273853517741389212936317027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182569011827592808624211351 273853517741389212936317027)
  ·
    refine ⟨410780276612083819404475541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273853517741389212936317027 410780276612083819404475541)
    ·
      refine ⟨19255325466191429034584791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 410780276612083819404475541 19255325466191429034584791)
      ·
        refine ⟨28882988199287143551877187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19255325466191429034584791 28882988199287143551877187)
        ·
          refine ⟨43324482298930715327815781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28882988199287143551877187 43324482298930715327815781)
          ·
            refine ⟨8123340431049509123965459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43324482298930715327815781 8123340431049509123965459)
            ·
              refine ⟨12185010646574263685948189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123340431049509123965459 12185010646574263685948189)
              ·
                refine ⟨4569378992465348882230571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12185010646574263685948189 4569378992465348882230571)
                ·
                  refine ⟨6854068488698023323345857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569378992465348882230571 6854068488698023323345857)
                  ·
                    refine ⟨5140551366523517492509393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6854068488698023323345857 5140551366523517492509393)
                    ·
                      refine ⟨3855413524892638119382045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140551366523517492509393 3855413524892638119382045)
                      ·
                        rfl

theorem cell23_7508391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_7508391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508391 prefixEnd_7508391 := by exact prefixLift 7508391
  have htrace : WordTrace (prefixWord ++ tailWord_7508391) baseStart_7508391 baseEnd_7508391 := by
    simpa [prefixWord, tailWord_7508391, baseEnd_7508391] using wordTrace_append hprefix tailTrace_7508391
  have hstable : (prefixWord ++ tailWord_7508391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508391).length < 2 ^ (prefixWord ++ tailWord_7508391).sum := by decide
  have hdescent : baseEnd_7508391 < baseStart_7508391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508394 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5]
def baseStart_7508394 : Nat := 118140960795 + 7508394 * 2 ^ 59
def prefixEnd_7508394 : Nat := 4983230072969 + 3 ^ 40 * 7508394 * 2
def baseEnd_7508394 : Nat := 3855415065334601607644531

theorem tailTrace_7508394 : CollatzResearch.WordTrace tailWord_7508394 prefixEnd_7508394 3855415065334601607644531 := by
  unfold tailWord_7508394
  simp only [CollatzResearch.WordTrace]
  refine ⟨68463406790094586112169059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182569084773585562965784157 68463406790094586112169059)
  ·
    refine ⟨102695110185141879168253589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68463406790094586112169059 102695110185141879168253589)
    ·
      refine ⟨4813833289928525586011887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102695110185141879168253589 4813833289928525586011887)
      ·
        refine ⟨7220749934892788379017831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4813833289928525586011887 7220749934892788379017831)
        ·
          refine ⟨10831124902339182568526747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7220749934892788379017831 10831124902339182568526747)
          ·
            refine ⟨16246687353508773852790121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10831124902339182568526747 16246687353508773852790121)
            ·
              refine ⟨12185015515131580389592591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16246687353508773852790121 12185015515131580389592591)
              ·
                refine ⟨18277523272697370584388887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12185015515131580389592591 18277523272697370584388887)
                ·
                  refine ⟨27416284909046055876583331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18277523272697370584388887 27416284909046055876583331)
                  ·
                    refine ⟨41124427363569083814874997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27416284909046055876583331 41124427363569083814874997)
                    ·
                      refine ⟨3855415065334601607644531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41124427363569083814874997 3855415065334601607644531)
                      ·
                        rfl

theorem cell23_7508394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_7508394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508394 prefixEnd_7508394 := by exact prefixLift 7508394
  have htrace : WordTrace (prefixWord ++ tailWord_7508394) baseStart_7508394 baseEnd_7508394 := by
    simpa [prefixWord, tailWord_7508394, baseEnd_7508394] using wordTrace_append hprefix tailTrace_7508394
  have hstable : (prefixWord ++ tailWord_7508394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508394).length < 2 ^ (prefixWord ++ tailWord_7508394).sum := by decide
  have hdescent : baseEnd_7508394 < baseStart_7508394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508396 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_7508396 : Nat := 118140960795 + 7508396 * 2 ^ 59
def prefixEnd_7508396 : Nat := 4983230072969 + 3 ^ 40 * 7508396 * 2
def baseEnd_7508396 : Nat := 3855416092295910599819521

theorem tailTrace_7508396 : CollatzResearch.WordTrace tailWord_7508396 prefixEnd_7508396 3855416092295910599819521 := by
  unfold tailWord_7508396
  simp only [CollatzResearch.WordTrace]
  refine ⟨136926850053185549395124521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182569133404247399193499361 136926850053185549395124521)
  ·
    refine ⟨102695137539889162046343391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136926850053185549395124521 102695137539889162046343391)
    ·
      refine ⟨154042706309833743069515087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102695137539889162046343391 154042706309833743069515087)
      ·
        refine ⟨231064059464750614604272631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154042706309833743069515087 231064059464750614604272631)
        ·
          refine ⟨346596089197125921906408947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231064059464750614604272631 346596089197125921906408947)
          ·
            refine ⟨519894133795688882859613421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346596089197125921906408947 519894133795688882859613421)
            ·
              refine ⟨194960300173383331072355033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519894133795688882859613421 194960300173383331072355033)
              ·
                refine ⟨146220225130037498304266275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194960300173383331072355033 146220225130037498304266275)
                ·
                  refine ⟨219330337695056247456399413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146220225130037498304266275 219330337695056247456399413)
                  ·
                    refine ⟨20562219158911523199037445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 219330337695056247456399413 20562219158911523199037445)
                    ·
                      refine ⟨3855416092295910599819521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20562219158911523199037445 3855416092295910599819521)
                      ·
                        rfl

theorem cell23_7508396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_7508396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508396 prefixEnd_7508396 := by exact prefixLift 7508396
  have htrace : WordTrace (prefixWord ++ tailWord_7508396) baseStart_7508396 baseEnd_7508396 := by
    simpa [prefixWord, tailWord_7508396, baseEnd_7508396] using wordTrace_append hprefix tailTrace_7508396
  have hstable : (prefixWord ++ tailWord_7508396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508396).length < 2 ^ (prefixWord ++ tailWord_7508396).sum := by decide
  have hdescent : baseEnd_7508396 < baseStart_7508396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508416 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_7508416 : Nat := 118140960795 + 7508416 * 2 ^ 59
def prefixEnd_7508416 : Nat := 4983230072969 + 3 ^ 40 * 7508416 * 2
def baseEnd_7508416 : Nat := 3855426361909000521569429

theorem tailTrace_7508416 : CollatzResearch.WordTrace tailWord_7508416 prefixEnd_7508416 3855426361909000521569429 := by
  unfold tailWord_7508416
  simp only [CollatzResearch.WordTrace]
  refine ⟨136927214783149321102988551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182569619710865761470651401 136927214783149321102988551)
  ·
    refine ⟨205390822174723981654482827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136927214783149321102988551 205390822174723981654482827)
    ·
      refine ⟨308086233262085972481724241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205390822174723981654482827 308086233262085972481724241)
      ·
        refine ⟨231064674946564479361293181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308086233262085972481724241 231064674946564479361293181)
        ·
          refine ⟨86649253104961679760484943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231064674946564479361293181 86649253104961679760484943)
          ·
            refine ⟨129973879657442519640727415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86649253104961679760484943 129973879657442519640727415)
            ·
              refine ⟨194960819486163779461091123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129973879657442519640727415 194960819486163779461091123)
              ·
                refine ⟨292441229229245669191636685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194960819486163779461091123 292441229229245669191636685)
                ·
                  refine ⟨109665460960967125946863757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292441229229245669191636685 109665460960967125946863757)
                  ·
                    refine ⟨41124547860362672230073909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109665460960967125946863757 41124547860362672230073909)
                    ·
                      refine ⟨3855426361909000521569429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41124547860362672230073909 3855426361909000521569429)
                      ·
                        rfl

theorem cell23_7508416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_7508416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508416 prefixEnd_7508416 := by exact prefixLift 7508416
  have htrace : WordTrace (prefixWord ++ tailWord_7508416) baseStart_7508416 baseEnd_7508416 := by
    simpa [prefixWord, tailWord_7508416, baseEnd_7508416] using wordTrace_append hprefix tailTrace_7508416
  have hstable : (prefixWord ++ tailWord_7508416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508416).length < 2 ^ (prefixWord ++ tailWord_7508416).sum := by decide
  have hdescent : baseEnd_7508416 < baseStart_7508416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508424 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_7508424 : Nat := 118140960795 + 7508424 * 2 ^ 59
def prefixEnd_7508424 : Nat := 4983230072969 + 3 ^ 40 * 7508424 * 2
def baseEnd_7508424 : Nat := 3855430469754236490269393

theorem tailTrace_7508424 : CollatzResearch.WordTrace tailWord_7508424 prefixEnd_7508424 3855430469754236490269393 := by
  unfold tailWord_7508424
  simp only [CollatzResearch.WordTrace]
  refine ⟨136927360675134829786134163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182569814233513106381512217 136927360675134829786134163)
  ·
    refine ⟨205391041012702244679201245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136927360675134829786134163 205391041012702244679201245)
    ·
      refine ⟨77021640379763341754700467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205391041012702244679201245 77021640379763341754700467)
      ·
        refine ⟨115532460569645012632050701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77021640379763341754700467 115532460569645012632050701)
        ·
          refine ⟨43324672713616879737019013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115532460569645012632050701 43324672713616879737019013)
          ·
            refine ⟨8123376133803164950691065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43324672713616879737019013 8123376133803164950691065)
            ·
              refine ⟨6092532100352373713018299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8123376133803164950691065 6092532100352373713018299)
              ·
                refine ⟨9138798150528560569527449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092532100352373713018299 9138798150528560569527449)
                ·
                  refine ⟨6854098612896420427145587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9138798150528560569527449 6854098612896420427145587)
                  ·
                    refine ⟨10281147919344630640718381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6854098612896420427145587 10281147919344630640718381)
                    ·
                      refine ⟨3855430469754236490269393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10281147919344630640718381 3855430469754236490269393)
                      ·
                        rfl

theorem cell23_7508424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_7508424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508424 prefixEnd_7508424 := by exact prefixLift 7508424
  have htrace : WordTrace (prefixWord ++ tailWord_7508424) baseStart_7508424 baseEnd_7508424 := by
    simpa [prefixWord, tailWord_7508424, baseEnd_7508424] using wordTrace_append hprefix tailTrace_7508424
  have hstable : (prefixWord ++ tailWord_7508424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508424).length < 2 ^ (prefixWord ++ tailWord_7508424).sum := by decide
  have hdescent : baseEnd_7508424 < baseStart_7508424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508430 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_7508430 : Nat := 118140960795 + 7508430 * 2 ^ 59
def prefixEnd_7508430 : Nat := 4983230072969 + 3 ^ 40 * 7508430 * 2
def baseEnd_7508430 : Nat := 3855433550638163466794365

theorem tailTrace_7508430 : CollatzResearch.WordTrace tailWord_7508430 prefixEnd_7508430 3855433550638163466794365 := by
  unfold tailWord_7508430
  simp only [CollatzResearch.WordTrace]
  refine ⟨34231867523530990324623343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182569960125498615064657829 34231867523530990324623343)
  ·
    refine ⟨51347801285296485486935015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34231867523530990324623343 51347801285296485486935015)
    ·
      refine ⟨77021701927944728230402523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51347801285296485486935015 77021701927944728230402523)
      ·
        refine ⟨115532552891917092345603785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77021701927944728230402523 115532552891917092345603785)
        ·
          refine ⟨86649414668937819259202839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115532552891917092345603785 86649414668937819259202839)
          ·
            refine ⟨129974122003406728888804259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86649414668937819259202839 129974122003406728888804259)
            ·
              refine ⟨194961183005110093333206389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129974122003406728888804259 194961183005110093333206389)
              ·
                refine ⟨18277610906729071249988099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194961183005110093333206389 18277610906729071249988099)
                ·
                  refine ⟨27416416360093606874982149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18277610906729071249988099 27416416360093606874982149)
                  ·
                    refine ⟨5140578067517551289059153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27416416360093606874982149 5140578067517551289059153)
                    ·
                      refine ⟨3855433550638163466794365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140578067517551289059153 3855433550638163466794365)
                      ·
                        rfl

theorem cell23_7508430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_7508430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508430 prefixEnd_7508430 := by exact prefixLift 7508430
  have htrace : WordTrace (prefixWord ++ tailWord_7508430) baseStart_7508430 baseEnd_7508430 := by
    simpa [prefixWord, tailWord_7508430, baseEnd_7508430] using wordTrace_append hprefix tailTrace_7508430
  have hstable : (prefixWord ++ tailWord_7508430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508430).length < 2 ^ (prefixWord ++ tailWord_7508430).sum := by decide
  have hdescent : baseEnd_7508430 < baseStart_7508430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508434 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7508434 : Nat := 118140960795 + 7508434 * 2 ^ 59
def prefixEnd_7508434 : Nat := 4983230072969 + 3 ^ 40 * 7508434 * 2
def baseEnd_7508434 : Nat := 3855435604560781451144347

theorem tailTrace_7508434 : CollatzResearch.WordTrace tailWord_7508434 prefixEnd_7508434 3855435604560781451144347 := by
  unfold tailWord_7508434
  simp only [CollatzResearch.WordTrace]
  refine ⟨68463771520058357820033089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182570057386822287520088237 68463771520058357820033089)
  ·
    refine ⟨51347828640043768365024817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68463771520058357820033089 51347828640043768365024817)
    ·
      refine ⟨38510871480032826273768613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51347828640043768365024817 38510871480032826273768613)
      ·
        refine ⟨7220788402506154926331615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38510871480032826273768613 7220788402506154926331615)
        ·
          refine ⟨10831182603759232389497423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7220788402506154926331615 10831182603759232389497423)
          ·
            refine ⟨16246773905638848584246135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10831182603759232389497423 16246773905638848584246135)
            ·
              refine ⟨24370160858458272876369203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16246773905638848584246135 24370160858458272876369203)
              ·
                refine ⟨36555241287687409314553805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24370160858458272876369203 36555241287687409314553805)
                ·
                  refine ⟨13708215482882778492957677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36555241287687409314553805 13708215482882778492957677)
                  ·
                    refine ⟨5140580806081041934859129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13708215482882778492957677 5140580806081041934859129)
                    ·
                      refine ⟨3855435604560781451144347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140580806081041934859129 3855435604560781451144347)
                      ·
                        rfl

theorem cell23_7508434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7508434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508434 prefixEnd_7508434 := by exact prefixLift 7508434
  have htrace : WordTrace (prefixWord ++ tailWord_7508434) baseStart_7508434 baseEnd_7508434 := by
    simpa [prefixWord, tailWord_7508434, baseEnd_7508434] using wordTrace_append hprefix tailTrace_7508434
  have hstable : (prefixWord ++ tailWord_7508434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508434).length < 2 ^ (prefixWord ++ tailWord_7508434).sum := by decide
  have hdescent : baseEnd_7508434 < baseStart_7508434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508463 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 3]
def baseStart_7508463 : Nat := 118140960795 + 7508463 * 2 ^ 59
def prefixEnd_7508463 : Nat := 4983230072969 + 3 ^ 40 * 7508463 * 2
def baseEnd_7508463 : Nat := 3855450495499761837681713

theorem tailTrace_7508463 : CollatzResearch.WordTrace tailWord_7508463 prefixEnd_7508463 3855450495499761837681713 := by
  unfold tailWord_7508463
  simp only [CollatzResearch.WordTrace]
  refine ⟨273856143797128369232938043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182570762531418912821958695 273856143797128369232938043)
  ·
    refine ⟨410784215695692553849407065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273856143797128369232938043 410784215695692553849407065)
    ·
      refine ⟨308088161771769415387055299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410784215695692553849407065 308088161771769415387055299)
      ·
        refine ⟨462132242657654123080582949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308088161771769415387055299 462132242657654123080582949)
        ·
          refine ⟨86649795498310148077609303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 462132242657654123080582949 86649795498310148077609303)
          ·
            refine ⟨129974693247465222116413955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86649795498310148077609303 129974693247465222116413955)
            ·
              refine ⟨194962039871197833174620933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129974693247465222116413955 194962039871197833174620933)
              ·
                refine ⟨36555382475849593720241425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194962039871197833174620933 36555382475849593720241425)
                ·
                  refine ⟨27416536856887195290181069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36555382475849593720241425 27416536856887195290181069)
                  ·
                    refine ⟨10281201321332698233817901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27416536856887195290181069 10281201321332698233817901)
                    ·
                      refine ⟨3855450495499761837681713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10281201321332698233817901 3855450495499761837681713)
                      ·
                        rfl

theorem cell23_7508463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_7508463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508463 prefixEnd_7508463 := by exact prefixLift 7508463
  have htrace : WordTrace (prefixWord ++ tailWord_7508463) baseStart_7508463 baseEnd_7508463 := by
    simpa [prefixWord, tailWord_7508463, baseEnd_7508463] using wordTrace_append hprefix tailTrace_7508463
  have hstable : (prefixWord ++ tailWord_7508463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508463).length < 2 ^ (prefixWord ++ tailWord_7508463).sum := by decide
  have hdescent : baseEnd_7508463 < baseStart_7508463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508490 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2]
def baseStart_7508490 : Nat := 118140960795 + 7508490 * 2 ^ 59
def prefixEnd_7508490 : Nat := 4983230072969 + 3 ^ 40 * 7508490 * 2
def baseEnd_7508490 : Nat := 3855464359477433232044089

theorem tailTrace_7508490 : CollatzResearch.WordTrace tailWord_7508490 prefixEnd_7508490 3855464359477433232044089 := by
  unfold tailWord_7508490
  simp only [CollatzResearch.WordTrace]
  refine ⟨68464282142007638211042731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182571419045353701896113949 68464282142007638211042731)
  ·
    refine ⟨102696423213011457316564097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68464282142007638211042731 102696423213011457316564097)
    ·
      refine ⟨77022317409758592987423073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102696423213011457316564097 77022317409758592987423073)
      ·
        refine ⟨57766738057318944740567305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77022317409758592987423073 57766738057318944740567305)
        ·
          refine ⟨43325053542989208555425479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57766738057318944740567305 43325053542989208555425479)
          ·
            refine ⟨64987580314483812833138219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43325053542989208555425479 64987580314483812833138219)
            ·
              refine ⟨97481370471725719249707329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64987580314483812833138219 97481370471725719249707329)
              ·
                refine ⟨73111027853794289437280497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97481370471725719249707329 73111027853794289437280497)
                ·
                  refine ⟨54833270890345717077960373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73111027853794289437280497 54833270890345717077960373)
                  ·
                    refine ⟨5140619145969910976058785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54833270890345717077960373 5140619145969910976058785)
                    ·
                      refine ⟨3855464359477433232044089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140619145969910976058785 3855464359477433232044089)
                      ·
                        rfl

theorem cell23_7508490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_7508490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508490 prefixEnd_7508490 := by exact prefixLift 7508490
  have htrace : WordTrace (prefixWord ++ tailWord_7508490) baseStart_7508490 baseEnd_7508490 := by
    simpa [prefixWord, tailWord_7508490, baseEnd_7508490] using wordTrace_append hprefix tailTrace_7508490
  have hstable : (prefixWord ++ tailWord_7508490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508490).length < 2 ^ (prefixWord ++ tailWord_7508490).sum := by decide
  have hdescent : baseEnd_7508490 < baseStart_7508490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508530 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_7508530 : Nat := 118140960795 + 7508530 * 2 ^ 59
def prefixEnd_7508530 : Nat := 4983230072969 + 3 ^ 40 * 7508530 * 2
def baseEnd_7508530 : Nat := 1285161632901204358514635

theorem tailTrace_7508530 : CollatzResearch.WordTrace tailWord_7508530 prefixEnd_7508530 1285161632901204358514635 := by
  unfold tailWord_7508530
  simp only [CollatzResearch.WordTrace]
  refine ⟨68464646871971409918906761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182572391658590426450418029 68464646871971409918906761)
  ·
    refine ⟨51348485153978557439180071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68464646871971409918906761 51348485153978557439180071)
    ·
      refine ⟨77022727730967836158770107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51348485153978557439180071 77022727730967836158770107)
      ·
        refine ⟨115534091596451754238155161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77022727730967836158770107 115534091596451754238155161)
        ·
          refine ⟨86650568697338815678616371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115534091596451754238155161 86650568697338815678616371)
          ·
            refine ⟨129975853046008223517924557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86650568697338815678616371 129975853046008223517924557)
            ·
              refine ⟨48740944892253083819221709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129975853046008223517924557 48740944892253083819221709)
              ·
                refine ⟨18277854334594906432208141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48740944892253083819221709 18277854334594906432208141)
                ·
                  refine ⟨6854195375473089912078053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18277854334594906432208141 6854195375473089912078053)
                  ·
                    refine ⟨1285161632901204358514635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854195375473089912078053 1285161632901204358514635)
                    ·
                      rfl

theorem cell23_7508530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_7508530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508530 prefixEnd_7508530 := by exact prefixLift 7508530
  have htrace : WordTrace (prefixWord ++ tailWord_7508530) baseStart_7508530 baseEnd_7508530 := by
    simpa [prefixWord, tailWord_7508530, baseEnd_7508530] using wordTrace_append hprefix tailTrace_7508530
  have hstable : (prefixWord ++ tailWord_7508530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508530).length < 2 ^ (prefixWord ++ tailWord_7508530).sum := by decide
  have hdescent : baseEnd_7508530 < baseStart_7508530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508533 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_7508533 : Nat := 118140960795 + 7508533 * 2 ^ 59
def prefixEnd_7508533 : Nat := 4983230072969 + 3 ^ 40 * 7508533 * 2
def baseEnd_7508533 : Nat := 3855486439145576563806391

theorem tailTrace_7508533 : CollatzResearch.WordTrace tailWord_7508533 prefixEnd_7508533 3855486439145576563806391 := by
  unfold tailWord_7508533
  simp only [CollatzResearch.WordTrace]
  refine ⟨273858696906874771187986253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182572464604583180791990835 273858696906874771187986253)
  ·
    refine ⟨102697011340078039195494845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273858696906874771187986253 102697011340078039195494845)
    ·
      refine ⟨38511379252529264698310567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102697011340078039195494845 38511379252529264698310567)
      ·
        refine ⟨57767068878793897047465851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38511379252529264698310567 57767068878793897047465851)
        ·
          refine ⟨86650603318190845571198777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57767068878793897047465851 86650603318190845571198777)
          ·
            refine ⟨64987952488643134178399083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86650603318190845571198777 64987952488643134178399083)
            ·
              refine ⟨97481928732964701267598625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64987952488643134178399083 97481928732964701267598625)
              ·
                refine ⟨73111446549723525950698969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97481928732964701267598625 73111446549723525950698969)
                ·
                  refine ⟨54833584912292644463024227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73111446549723525950698969 54833584912292644463024227)
                  ·
                    refine ⟨82250377368438966694536341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54833584912292644463024227 82250377368438966694536341)
                    ·
                      refine ⟨3855486439145576563806391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82250377368438966694536341 3855486439145576563806391)
                      ·
                        rfl

theorem cell23_7508533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_7508533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508533 prefixEnd_7508533 := by exact prefixLift 7508533
  have htrace : WordTrace (prefixWord ++ tailWord_7508533) baseStart_7508533 baseEnd_7508533 := by
    simpa [prefixWord, tailWord_7508533, baseEnd_7508533] using wordTrace_append hprefix tailTrace_7508533
  have hstable : (prefixWord ++ tailWord_7508533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508533).length < 2 ^ (prefixWord ++ tailWord_7508533).sum := by decide
  have hdescent : baseEnd_7508533 < baseStart_7508533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508540 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_7508540 : Nat := 118140960795 + 7508540 * 2 ^ 59
def prefixEnd_7508540 : Nat := 4983230072969 + 3 ^ 40 * 7508540 * 2
def baseEnd_7508540 : Nat := 3855490033510158036418859

theorem tailTrace_7508540 : CollatzResearch.WordTrace tailWord_7508540 prefixEnd_7508540 3855490033510158036418859 := by
  unfold tailWord_7508540
  simp only [CollatzResearch.WordTrace]
  refine ⟨136929476108924705691745537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182572634811899607588994049 136929476108924705691745537)
  ·
    refine ⟨102697107081693529268809153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136929476108924705691745537 102697107081693529268809153)
    ·
      refine ⟨77022830311270146951606865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102697107081693529268809153 77022830311270146951606865)
      ·
        refine ⟨57767122733452610213705149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77022830311270146951606865 57767122733452610213705149)
        ·
          refine ⟨21662671025044728830139431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57767122733452610213705149 21662671025044728830139431)
          ·
            refine ⟨32494006537567093245209147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21662671025044728830139431 32494006537567093245209147)
            ·
              refine ⟨48741009806350639867813721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32494006537567093245209147 48741009806350639867813721)
              ·
                refine ⟨36555757354762979900860291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48741009806350639867813721 36555757354762979900860291)
                ·
                  refine ⟨54833636032144469851290437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36555757354762979900860291 54833636032144469851290437)
                  ·
                    refine ⟨10281306756027088097116957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54833636032144469851290437 10281306756027088097116957)
                    ·
                      refine ⟨3855490033510158036418859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10281306756027088097116957 3855490033510158036418859)
                      ·
                        rfl

theorem cell23_7508540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_7508540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508540 prefixEnd_7508540 := by exact prefixLift 7508540
  have htrace : WordTrace (prefixWord ++ tailWord_7508540) baseStart_7508540 baseEnd_7508540 := by
    simpa [prefixWord, tailWord_7508540, baseEnd_7508540] using wordTrace_append hprefix tailTrace_7508540
  have hstable : (prefixWord ++ tailWord_7508540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508540).length < 2 ^ (prefixWord ++ tailWord_7508540).sum := by decide
  have hdescent : baseEnd_7508540 < baseStart_7508540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508557 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_7508557 : Nat := 118140960795 + 7508557 * 2 ^ 59
def prefixEnd_7508557 : Nat := 4983230072969 + 3 ^ 40 * 7508557 * 2
def baseEnd_7508557 : Nat := 3855498762681284469906281

theorem tailTrace_7508557 : CollatzResearch.WordTrace tailWord_7508557 prefixEnd_7508557 3855498762681284469906281 := by
  unfold tailWord_7508557
  simp only [CollatzResearch.WordTrace]
  refine ⟨273859572258787823286859925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182573048172525215524573283 273859572258787823286859925)
  ·
    refine ⟨12837167449630679216571559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 273859572258787823286859925 12837167449630679216571559)
    ·
      refine ⟨19255751174446018824857339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12837167449630679216571559 19255751174446018824857339)
      ·
        refine ⟨28883626761669028237286009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19255751174446018824857339 28883626761669028237286009)
        ·
          refine ⟨21662720071251771177964507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28883626761669028237286009 21662720071251771177964507)
          ·
            refine ⟨32494080106877656766946761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21662720071251771177964507 32494080106877656766946761)
            ·
              refine ⟨24370560080158242575210071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32494080106877656766946761 24370560080158242575210071)
              ·
                refine ⟨36555840120237363862815107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24370560080158242575210071 36555840120237363862815107)
                ·
                  refine ⟨54833760180356045794222661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36555840120237363862815107 54833760180356045794222661)
                  ·
                    refine ⟨10281330033816758586416749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54833760180356045794222661 10281330033816758586416749)
                    ·
                      refine ⟨3855498762681284469906281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10281330033816758586416749 3855498762681284469906281)
                      ·
                        rfl

theorem cell23_7508557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_7508557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508557 prefixEnd_7508557 := by exact prefixLift 7508557
  have htrace : WordTrace (prefixWord ++ tailWord_7508557) baseStart_7508557 baseEnd_7508557 := by
    simpa [prefixWord, tailWord_7508557, baseEnd_7508557] using wordTrace_append hprefix tailTrace_7508557
  have hstable : (prefixWord ++ tailWord_7508557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508557).length < 2 ^ (prefixWord ++ tailWord_7508557).sum := by decide
  have hdescent : baseEnd_7508557 < baseStart_7508557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508564 : List Nat := [2, 4, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_7508564 : Nat := 118140960795 + 7508564 * 2 ^ 59
def prefixEnd_7508564 : Nat := 4983230072969 + 3 ^ 40 * 7508564 * 2
def baseEnd_7508564 : Nat := 1285167452348621980839583

theorem tailTrace_7508564 : CollatzResearch.WordTrace tailWord_7508564 prefixEnd_7508564 1285167452348621980839583 := by
  unfold tailWord_7508564
  simp only [CollatzResearch.WordTrace]
  refine ⟨136929913784881231741182373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182573218379841642321576497 136929913784881231741182373)
  ·
    refine ⟨25674358834665230951471695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136929913784881231741182373 25674358834665230951471695)
    ·
      refine ⟨38511538251997846427207543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25674358834665230951471695 38511538251997846427207543)
      ·
        refine ⟨57767307377996769640811315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38511538251997846427207543 57767307377996769640811315)
        ·
          refine ⟨86650961066995154461216973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57767307377996769640811315 86650961066995154461216973)
          ·
            refine ⟨32494110400123182922956365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86650961066995154461216973 32494110400123182922956365)
            ·
              refine ⟨12185291400046193596108637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32494110400123182922956365 12185291400046193596108637)
              ·
                refine ⟨4569484275017322598540739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12185291400046193596108637 4569484275017322598540739)
                ·
                  refine ⟨6854226412525983897811109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569484275017322598540739 6854226412525983897811109)
                  ·
                    refine ⟨1285167452348621980839583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854226412525983897811109 1285167452348621980839583)
                    ·
                      rfl

theorem cell23_7508564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_7508564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508564 prefixEnd_7508564 := by exact prefixLift 7508564
  have htrace : WordTrace (prefixWord ++ tailWord_7508564) baseStart_7508564 baseEnd_7508564 := by
    simpa [prefixWord, tailWord_7508564, baseEnd_7508564] using wordTrace_append hprefix tailTrace_7508564
  have hstable : (prefixWord ++ tailWord_7508564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508564).length < 2 ^ (prefixWord ++ tailWord_7508564).sum := by decide
  have hdescent : baseEnd_7508564 < baseStart_7508564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508581 : List Nat := [1, 3, 1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_7508581 : Nat := 118140960795 + 7508581 * 2 ^ 59
def prefixEnd_7508581 : Nat := 4983230072969 + 3 ^ 40 * 7508581 * 2
def baseEnd_7508581 : Nat := 1285170362072330792002057

theorem tailTrace_7508581 : CollatzResearch.WordTrace tailWord_7508581 prefixEnd_7508581 1285170362072330792002057 := by
  unfold tailWord_7508581
  simp only [CollatzResearch.WordTrace]
  refine ⟨273860447610700875385733597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182573631740467250257155731 273860447610700875385733597)
  ·
    refine ⟨102697667854012828269650099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273860447610700875385733597 102697667854012828269650099)
    ·
      refine ⟨154046501781019242404475149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102697667854012828269650099 154046501781019242404475149)
      ·
        refine ⟨57767438167882215901678181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154046501781019242404475149 57767438167882215901678181)
        ·
          refine ⟨10831394656477915481564659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57767438167882215901678181 10831394656477915481564659)
          ·
            refine ⟨16247091984716873222346989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10831394656477915481564659 16247091984716873222346989)
            ·
              refine ⟨6092659494268827458380121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16247091984716873222346989 6092659494268827458380121)
              ·
                refine ⟨4569494620701620593785091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6092659494268827458380121 4569494620701620593785091)
                ·
                  refine ⟨6854241931052430890677637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569494620701620593785091 6854241931052430890677637)
                  ·
                    refine ⟨1285170362072330792002057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854241931052430890677637 1285170362072330792002057)
                    ·
                      rfl

theorem cell23_7508581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_7508581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508581 prefixEnd_7508581 := by exact prefixLift 7508581
  have htrace : WordTrace (prefixWord ++ tailWord_7508581) baseStart_7508581 baseEnd_7508581 := by
    simpa [prefixWord, tailWord_7508581, baseEnd_7508581] using wordTrace_append hprefix tailTrace_7508581
  have hstable : (prefixWord ++ tailWord_7508581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508581).length < 2 ^ (prefixWord ++ tailWord_7508581).sum := by decide
  have hdescent : baseEnd_7508581 < baseStart_7508581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508583 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_7508583 : Nat := 118140960795 + 7508583 * 2 ^ 59
def prefixEnd_7508583 : Nat := 4983230072969 + 3 ^ 40 * 7508583 * 2
def baseEnd_7508583 : Nat := 3855512113178301368181161

theorem tailTrace_7508583 : CollatzResearch.WordTrace tailWord_7508583 prefixEnd_7508583 3855512113178301368181161 := by
  unfold tailWord_7508583
  simp only [CollatzResearch.WordTrace]
  refine ⟨273860520556693629727306403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182573680371129086484870935 273860520556693629727306403)
  ·
    refine ⟨410790780835040444590959605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273860520556693629727306403 410790780835040444590959605)
    ·
      refine ⟨38511635703285041680402463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 410790780835040444590959605 38511635703285041680402463)
      ·
        refine ⟨57767453554927562520603695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38511635703285041680402463 57767453554927562520603695)
        ·
          refine ⟨86651180332391343780905543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57767453554927562520603695 86651180332391343780905543)
          ·
            refine ⟨129976770498587015671358315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86651180332391343780905543 129976770498587015671358315)
            ·
              refine ⟨194965155747880523507037473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129976770498587015671358315 194965155747880523507037473)
              ·
                refine ⟨146223866810910392630278105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194965155747880523507037473 146223866810910392630278105)
                ·
                  refine ⟨109667900108182794472708579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146223866810910392630278105 109667900108182794472708579)
                  ·
                    refine ⟨164501850162274191709062869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109667900108182794472708579 164501850162274191709062869)
                    ·
                      refine ⟨3855512113178301368181161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164501850162274191709062869 3855512113178301368181161)
                      ·
                        rfl

theorem cell23_7508583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_7508583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508583 prefixEnd_7508583 := by exact prefixLift 7508583
  have htrace : WordTrace (prefixWord ++ tailWord_7508583) baseStart_7508583 baseEnd_7508583 := by
    simpa [prefixWord, tailWord_7508583, baseEnd_7508583] using wordTrace_append hprefix tailTrace_7508583
  have hstable : (prefixWord ++ tailWord_7508583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508583).length < 2 ^ (prefixWord ++ tailWord_7508583).sum := by decide
  have hdescent : baseEnd_7508583 < baseStart_7508583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508593 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_7508593 : Nat := 118140960795 + 7508593 * 2 ^ 59
def prefixEnd_7508593 : Nat := 4983230072969 + 3 ^ 40 * 7508593 * 2
def baseEnd_7508593 : Nat := 3855517247984846329056115

theorem tailTrace_7508593 : CollatzResearch.WordTrace tailWord_7508593 prefixEnd_7508593 3855517247984846329056115 := by
  unfold tailWord_7508593
  simp only [CollatzResearch.WordTrace]
  refine ⟨273860885286657401435170433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182573923524438267623446955 273860885286657401435170433)
  ·
    refine ⟨205395663964993051076377825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273860885286657401435170433 205395663964993051076377825)
    ·
      refine ⟨154046747973744788307283369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205395663964993051076377825 154046747973744788307283369)
      ·
        refine ⟨115535060980308591230462527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154046747973744788307283369 115535060980308591230462527)
        ·
          refine ⟨173302591470462886845693791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115535060980308591230462527 173302591470462886845693791)
          ·
            refine ⟨259953887205694330268540687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173302591470462886845693791 259953887205694330268540687)
            ·
              refine ⟨389930830808541495402811031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259953887205694330268540687 389930830808541495402811031)
              ·
                refine ⟨584896246212812243104216547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389930830808541495402811031 584896246212812243104216547)
                ·
                  refine ⟨877344369319218364656324821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584896246212812243104216547 877344369319218364656324821)
                  ·
                    refine ⟨20562758655919180421632613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 877344369319218364656324821 20562758655919180421632613)
                    ·
                      refine ⟨3855517247984846329056115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20562758655919180421632613 3855517247984846329056115)
                      ·
                        rfl

theorem cell23_7508593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_7508593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508593 prefixEnd_7508593 := by exact prefixLift 7508593
  have htrace : WordTrace (prefixWord ++ tailWord_7508593) baseStart_7508593 baseEnd_7508593 := by
    simpa [prefixWord, tailWord_7508593, baseEnd_7508593] using wordTrace_append hprefix tailTrace_7508593
  have hstable : (prefixWord ++ tailWord_7508593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508593).length < 2 ^ (prefixWord ++ tailWord_7508593).sum := by decide
  have hdescent : baseEnd_7508593 < baseStart_7508593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508594 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 6]
def baseStart_7508594 : Nat := 118140960795 + 7508594 * 2 ^ 59
def prefixEnd_7508594 : Nat := 4983230072969 + 3 ^ 40 * 7508594 * 2
def baseEnd_7508594 : Nat := 428390862385055647238179

theorem tailTrace_7508594 : CollatzResearch.WordTrace tailWord_7508594 prefixEnd_7508594 428390862385055647238179 := by
  unfold tailWord_7508594
  simp only [CollatzResearch.WordTrace]
  refine ⟨68465230439913444651489209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182573947839769185737304557 68465230439913444651489209)
  ·
    refine ⟨51348922829935083488616907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68465230439913444651489209 51348922829935083488616907)
    ·
      refine ⟨77023384244902625232925361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51348922829935083488616907 77023384244902625232925361)
      ·
        refine ⟨57767538183676968924694021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77023384244902625232925361 57767538183676968924694021)
        ·
          refine ⟨10831413409439431673380129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57767538183676968924694021 10831413409439431673380129)
          ·
            refine ⟨8123560057079573755035097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10831413409439431673380129 8123560057079573755035097)
            ·
              refine ⟨6092670042809680316276323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8123560057079573755035097 6092670042809680316276323)
              ·
                refine ⟨9139005064214520474414485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092670042809680316276323 9139005064214520474414485)
                ·
                  refine ⟨428390862385055647238179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9139005064214520474414485 428390862385055647238179)
                  ·
                    rfl

theorem cell23_7508594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_7508594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508594 prefixEnd_7508594 := by exact prefixLift 7508594
  have htrace : WordTrace (prefixWord ++ tailWord_7508594) baseStart_7508594 baseEnd_7508594 := by
    simpa [prefixWord, tailWord_7508594, baseEnd_7508594] using wordTrace_append hprefix tailTrace_7508594
  have hstable : (prefixWord ++ tailWord_7508594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508594).length < 2 ^ (prefixWord ++ tailWord_7508594).sum := by decide
  have hdescent : baseEnd_7508594 < baseStart_7508594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508620 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_7508620 : Nat := 118140960795 + 7508620 * 2 ^ 59
def prefixEnd_7508620 : Nat := 4983230072969 + 3 ^ 40 * 7508620 * 2
def baseEnd_7508620 : Nat := 1285177037320839241139497

theorem tailTrace_7508620 : CollatzResearch.WordTrace tailWord_7508620 prefixEnd_7508620 1285177037320839241139497 := by
  unfold tailWord_7508620
  simp only [CollatzResearch.WordTrace]
  refine ⟨136930935028779792523201657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182574580038373056697602209 136930935028779792523201657)
  ·
    refine ⟨102698201271584844392401243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136930935028779792523201657 102698201271584844392401243)
    ·
      refine ⟨154047301907377266588601865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102698201271584844392401243 154047301907377266588601865)
      ·
        refine ⟨115535476430532949941451399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154047301907377266588601865 115535476430532949941451399)
        ·
          refine ⟨173303214645799424912177099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115535476430532949941451399 173303214645799424912177099)
          ·
            refine ⟨259954821968699137368265649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173303214645799424912177099 259954821968699137368265649)
            ·
              refine ⟨194966116476524353026199237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259954821968699137368265649 194966116476524353026199237)
              ·
                refine ⟨36556146839348316192412357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194966116476524353026199237 36556146839348316192412357)
                ·
                  refine ⟨6854277532377809286077317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36556146839348316192412357 6854277532377809286077317)
                  ·
                    refine ⟨1285177037320839241139497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854277532377809286077317 1285177037320839241139497)
                    ·
                      rfl

theorem cell23_7508620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_7508620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508620 prefixEnd_7508620 := by exact prefixLift 7508620
  have htrace : WordTrace (prefixWord ++ tailWord_7508620) baseStart_7508620 baseEnd_7508620 := by
    simpa [prefixWord, tailWord_7508620, baseEnd_7508620] using wordTrace_append hprefix tailTrace_7508620
  have hstable : (prefixWord ++ tailWord_7508620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508620).length < 2 ^ (prefixWord ++ tailWord_7508620).sum := by decide
  have hdescent : baseEnd_7508620 < baseStart_7508620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508627 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 5, 2, 2]
def baseStart_7508627 : Nat := 118140960795 + 7508627 * 2 ^ 59
def prefixEnd_7508627 : Nat := 4983230072969 + 3 ^ 40 * 7508627 * 2
def baseEnd_7508627 : Nat := 3855534706327099196030959

theorem tailTrace_7508627 : CollatzResearch.WordTrace tailWord_7508627 prefixEnd_7508627 3855534706327099196030959 := by
  unfold tailWord_7508627
  simp only [CollatzResearch.WordTrace]
  refine ⟨273862125368534225241908135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182574750245689483494605423 273862125368534225241908135)
  ·
    refine ⟨410793188052801337862862203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273862125368534225241908135 410793188052801337862862203)
    ·
      refine ⟨616189782079202006794293305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410793188052801337862862203 616189782079202006794293305)
      ·
        refine ⟨462142336559401505095719979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616189782079202006794293305 462142336559401505095719979)
        ·
          refine ⟨693213504839102257643579969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462142336559401505095719979 693213504839102257643579969)
          ·
            refine ⟨519910128629326693232684977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693213504839102257643579969 519910128629326693232684977)
            ·
              refine ⟨389932596471995019924513733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519910128629326693232684977 389932596471995019924513733)
              ·
                refine ⟨73112361838499066235846325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389932596471995019924513733 73112361838499066235846325)
                ·
                  refine ⟨6854283922359287459610593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73112361838499066235846325 6854283922359287459610593)
                  ·
                    refine ⟨5140712941769465594707945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6854283922359287459610593 5140712941769465594707945)
                    ·
                      refine ⟨3855534706327099196030959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140712941769465594707945 3855534706327099196030959)
                      ·
                        rfl

theorem cell23_7508627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 2, 2].length) (baseStart_7508627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508627 prefixEnd_7508627 := by exact prefixLift 7508627
  have htrace : WordTrace (prefixWord ++ tailWord_7508627) baseStart_7508627 baseEnd_7508627 := by
    simpa [prefixWord, tailWord_7508627, baseEnd_7508627] using wordTrace_append hprefix tailTrace_7508627
  have hstable : (prefixWord ++ tailWord_7508627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508627).length < 2 ^ (prefixWord ++ tailWord_7508627).sum := by decide
  have hdescent : baseEnd_7508627 < baseStart_7508627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508637 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_7508637 : Nat := 118140960795 + 7508637 * 2 ^ 59
def prefixEnd_7508637 : Nat := 4983230072969 + 3 ^ 40 * 7508637 * 2
def baseEnd_7508637 : Nat := 1285179947044548052301971

theorem tailTrace_7508637 : CollatzResearch.WordTrace tailWord_7508637 prefixEnd_7508637 1285179947044548052301971 := by
  unfold tailWord_7508637
  simp only [CollatzResearch.WordTrace]
  refine ⟨273862490098497996949772165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182574993398998664633181443 273862490098497996949772165)
  ·
    refine ⟨51349216893468374428082281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273862490098497996949772165 51349216893468374428082281)
    ·
      refine ⟨38511912670101280821061711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51349216893468374428082281 38511912670101280821061711)
      ·
        refine ⟨57767869005151921231592567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38511912670101280821061711 57767869005151921231592567)
        ·
          refine ⟨86651803507727881847388851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57767869005151921231592567 86651803507727881847388851)
          ·
            refine ⟨129977705261591822771083277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86651803507727881847388851 129977705261591822771083277)
            ·
              refine ⟨48741639473096933539156229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129977705261591822771083277 48741639473096933539156229)
              ·
                refine ⟨9139057401205675038591793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48741639473096933539156229 9139057401205675038591793)
                ·
                  refine ⟨6854293050904256278943845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9139057401205675038591793 6854293050904256278943845)
                  ·
                    refine ⟨1285179947044548052301971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854293050904256278943845 1285179947044548052301971)
                    ·
                      rfl

theorem cell23_7508637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_7508637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508637 prefixEnd_7508637 := by exact prefixLift 7508637
  have htrace : WordTrace (prefixWord ++ tailWord_7508637) baseStart_7508637 baseEnd_7508637 := by
    simpa [prefixWord, tailWord_7508637, baseEnd_7508637] using wordTrace_append hprefix tailTrace_7508637
  have hstable : (prefixWord ++ tailWord_7508637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508637).length < 2 ^ (prefixWord ++ tailWord_7508637).sum := by decide
  have hdescent : baseEnd_7508637 < baseStart_7508637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508643 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 7]
def baseStart_7508643 : Nat := 118140960795 + 7508643 * 2 ^ 59
def prefixEnd_7508643 : Nat := 4983230072969 + 3 ^ 40 * 7508643 * 2
def baseEnd_7508643 : Nat := 3855542922017571133430885

theorem tailTrace_7508643 : CollatzResearch.WordTrace tailWord_7508643 prefixEnd_7508643 3855542922017571133430885 := by
  unfold tailWord_7508643
  simp only [CollatzResearch.WordTrace]
  refine ⟨273862708936476259974490583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182575139290984173316327055 273862708936476259974490583)
  ·
    refine ⟨410794063404714389961735875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273862708936476259974490583 410794063404714389961735875)
    ·
      refine ⟨616191095107071584942603813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410794063404714389961735875 616191095107071584942603813)
      ·
        refine ⟨115535830332575922176738215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 616191095107071584942603813 115535830332575922176738215)
        ·
          refine ⟨173303745498863883265107323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115535830332575922176738215 173303745498863883265107323)
          ·
            refine ⟨259955618248295824897660985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173303745498863883265107323 259955618248295824897660985)
            ·
              refine ⟨194966713686221868673245739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259955618248295824897660985 194966713686221868673245739)
              ·
                refine ⟨292450070529332803009868609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194966713686221868673245739 292450070529332803009868609)
                ·
                  refine ⟨219337552896999602257401457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292450070529332803009868609 219337552896999602257401457)
                  ·
                    refine ⟨164503164672749701693051093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219337552896999602257401457 164503164672749701693051093)
                    ·
                      refine ⟨3855542922017571133430885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164503164672749701693051093 3855542922017571133430885)
                      ·
                        rfl

theorem cell23_7508643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_7508643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508643 prefixEnd_7508643 := by exact prefixLift 7508643
  have htrace : WordTrace (prefixWord ++ tailWord_7508643) baseStart_7508643 baseEnd_7508643 := by
    simpa [prefixWord, tailWord_7508643, baseEnd_7508643] using wordTrace_append hprefix tailTrace_7508643
  have hstable : (prefixWord ++ tailWord_7508643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508643).length < 2 ^ (prefixWord ++ tailWord_7508643).sum := by decide
  have hdescent : baseEnd_7508643 < baseStart_7508643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508644 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_7508644 : Nat := 118140960795 + 7508644 * 2 ^ 59
def prefixEnd_7508644 : Nat := 4983230072969 + 3 ^ 40 * 7508644 * 2
def baseEnd_7508644 : Nat := 3855543435498225629518381

theorem tailTrace_7508644 : CollatzResearch.WordTrace tailWord_7508644 prefixEnd_7508644 3855543435498225629518381 := by
  unfold tailWord_7508644
  simp only [CollatzResearch.WordTrace]
  refine ⟨136931372704736318572638493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182575163606315091430184657 136931372704736318572638493)
  ·
    refine ⟨51349264764276119464739435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136931372704736318572638493 51349264764276119464739435)
    ·
      refine ⟨77023897146414179197109153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51349264764276119464739435 77023897146414179197109153)
      ·
        refine ⟨57767922859810634397831865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77023897146414179197109153 57767922859810634397831865)
        ·
          refine ⟨43325942144857975798373899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57767922859810634397831865 43325942144857975798373899)
          ·
            refine ⟨64988913217286963697560849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43325942144857975798373899 64988913217286963697560849)
            ·
              refine ⟨48741684912965222773170637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64988913217286963697560849 48741684912965222773170637)
              ·
                refine ⟨18278131842361958539938989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48741684912965222773170637 18278131842361958539938989)
                ·
                  refine ⟨6854299440885734452477121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18278131842361958539938989 6854299440885734452477121)
                  ·
                    refine ⟨5140724580664300839357841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6854299440885734452477121 5140724580664300839357841)
                    ·
                      refine ⟨3855543435498225629518381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140724580664300839357841 3855543435498225629518381)
                      ·
                        rfl

theorem cell23_7508644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_7508644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508644 prefixEnd_7508644 := by exact prefixLift 7508644
  have htrace : WordTrace (prefixWord ++ tailWord_7508644) baseStart_7508644 baseEnd_7508644 := by
    simpa [prefixWord, tailWord_7508644, baseEnd_7508644] using wordTrace_append hprefix tailTrace_7508644
  have hstable : (prefixWord ++ tailWord_7508644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508644).length < 2 ^ (prefixWord ++ tailWord_7508644).sum := by decide
  have hdescent : baseEnd_7508644 < baseStart_7508644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508654 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_7508654 : Nat := 118140960795 + 7508654 * 2 ^ 59
def prefixEnd_7508654 : Nat := 4983230072969 + 3 ^ 40 * 7508654 * 2
def baseEnd_7508654 : Nat := 1285182856768256863464445

theorem tailTrace_7508654 : CollatzResearch.WordTrace tailWord_7508654 prefixEnd_7508654 1285182856768256863464445 := by
  unfold tailWord_7508654
  simp only [CollatzResearch.WordTrace]
  refine ⟨34232888767429551106642627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182575406759624272568760677 34232888767429551106642627)
  ·
    refine ⟨51349333151144326659963941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34232888767429551106642627 51349333151144326659963941)
    ·
      refine ⟨9627999965839561248743239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51349333151144326659963941 9627999965839561248743239)
      ·
        refine ⟨14441999948759341873114859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9627999965839561248743239 14441999948759341873114859)
        ·
          refine ⟨21662999923139012809672289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14441999948759341873114859 21662999923139012809672289)
          ·
            refine ⟨16247249942354259607254217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21662999923139012809672289 16247249942354259607254217)
            ·
              refine ⟨12185437456765694705440663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16247249942354259607254217 12185437456765694705440663)
              ·
                refine ⟨18278156185148542058160995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12185437456765694705440663 18278156185148542058160995)
                ·
                  refine ⟨27417234277722813087241493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18278156185148542058160995 27417234277722813087241493)
                  ·
                    refine ⟨1285182856768256863464445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27417234277722813087241493 1285182856768256863464445)
                    ·
                      rfl

theorem cell23_7508654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_7508654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508654 prefixEnd_7508654 := by exact prefixLift 7508654
  have htrace : WordTrace (prefixWord ++ tailWord_7508654) baseStart_7508654 baseEnd_7508654 := by
    simpa [prefixWord, tailWord_7508654, baseEnd_7508654] using wordTrace_append hprefix tailTrace_7508654
  have hstable : (prefixWord ++ tailWord_7508654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508654).length < 2 ^ (prefixWord ++ tailWord_7508654).sum := by decide
  have hdescent : baseEnd_7508654 < baseStart_7508654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508661 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_7508661 : Nat := 118140960795 + 7508661 * 2 ^ 59
def prefixEnd_7508661 : Nat := 4983230072969 + 3 ^ 40 * 7508661 * 2
def baseEnd_7508661 : Nat := 3855552164669352063005803

theorem tailTrace_7508661 : CollatzResearch.WordTrace tailWord_7508661 prefixEnd_7508661 3855552164669352063005803 := by
  unfold tailWord_7508661
  simp only [CollatzResearch.WordTrace]
  refine ⟨273863365450411049048645837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182575576966940699365763891 273863365450411049048645837)
  ·
    refine ⟨102698762043904143393242189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273863365450411049048645837 102698762043904143393242189)
    ·
      refine ⟨38512035766464053772465821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102698762043904143393242189 38512035766464053772465821)
      ·
        refine ⟨14442013412424020164674683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38512035766464053772465821 14442013412424020164674683)
        ·
          refine ⟨21663020118636030247012025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14442013412424020164674683 21663020118636030247012025)
          ·
            refine ⟨16247265088977022685259019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21663020118636030247012025 16247265088977022685259019)
            ·
              refine ⟨24370897633465534027888529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16247265088977022685259019 24370897633465534027888529)
              ·
                refine ⟨18278173225099150520916397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24370897633465534027888529 18278173225099150520916397)
                ·
                  refine ⟨6854314959412181445343649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18278173225099150520916397 6854314959412181445343649)
                  ·
                    refine ⟨5140736219559136084007737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6854314959412181445343649 5140736219559136084007737)
                    ·
                      refine ⟨3855552164669352063005803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140736219559136084007737 3855552164669352063005803)
                      ·
                        rfl

theorem cell23_7508661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_7508661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508661 prefixEnd_7508661 := by exact prefixLift 7508661
  have htrace : WordTrace (prefixWord ++ tailWord_7508661) baseStart_7508661 baseEnd_7508661 := by
    simpa [prefixWord, tailWord_7508661, baseEnd_7508661] using wordTrace_append hprefix tailTrace_7508661
  have hstable : (prefixWord ++ tailWord_7508661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508661).length < 2 ^ (prefixWord ++ tailWord_7508661).sum := by decide
  have hdescent : baseEnd_7508661 < baseStart_7508661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508678 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_7508678 : Nat := 118140960795 + 7508678 * 2 ^ 59
def prefixEnd_7508678 : Nat := 4983230072969 + 3 ^ 40 * 7508678 * 2
def baseEnd_7508678 : Nat := 3855560893840478496493225

theorem tailTrace_7508678 : CollatzResearch.WordTrace tailWord_7508678 prefixEnd_7508678 3855560893840478496493225 := by
  unfold tailWord_7508678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558249546604670654750459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182575990327566307301343125 8558249546604670654750459)
  ·
    refine ⟨12837374319907005982125689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8558249546604670654750459 12837374319907005982125689)
    ·
      refine ⟨9628030739930254486594267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12837374319907005982125689 9628030739930254486594267)
      ·
        refine ⟨14442046109895381729891401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9628030739930254486594267 14442046109895381729891401)
        ·
          refine ⟨10831534582421536297418551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14442046109895381729891401 10831534582421536297418551)
          ·
            refine ⟨16247301873632304446127827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10831534582421536297418551 16247301873632304446127827)
            ·
              refine ⟨24370952810448456669191741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16247301873632304446127827 24370952810448456669191741)
              ·
                refine ⟨9139107303918171250946903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24370952810448456669191741 9139107303918171250946903)
                ·
                  refine ⟨13708660955877256876420355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9139107303918171250946903 13708660955877256876420355)
                  ·
                    refine ⟨20562991433815885314630533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13708660955877256876420355 20562991433815885314630533)
                    ·
                      refine ⟨3855560893840478496493225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20562991433815885314630533 3855560893840478496493225)
                      ·
                        rfl

theorem cell23_7508678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_7508678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508678 prefixEnd_7508678 := by exact prefixLift 7508678
  have htrace : WordTrace (prefixWord ++ tailWord_7508678) baseStart_7508678 baseEnd_7508678 := by
    simpa [prefixWord, tailWord_7508678, baseEnd_7508678] using wordTrace_append hprefix tailTrace_7508678
  have hstable : (prefixWord ++ tailWord_7508678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508678).length < 2 ^ (prefixWord ++ tailWord_7508678).sum := by decide
  have hdescent : baseEnd_7508678 < baseStart_7508678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508720 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_7508720 : Nat := 118140960795 + 7508720 * 2 ^ 59
def prefixEnd_7508720 : Nat := 4983230072969 + 3 ^ 40 * 7508720 * 2
def baseEnd_7508720 : Nat := 3855582460027967332168031

theorem tailTrace_7508720 : CollatzResearch.WordTrace tailWord_7508720 prefixEnd_7508720 3855582460027967332168031 := by
  unfold tailWord_7508720
  simp only [CollatzResearch.WordTrace]
  refine ⟨136932758678598651062521807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182577011571464868083362409 136932758678598651062521807)
  ·
    refine ⟨205399138017897976593782711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136932758678598651062521807 205399138017897976593782711)
    ·
      refine ⟨308098707026846964890674067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205399138017897976593782711 308098707026846964890674067)
      ·
        refine ⟨462148060540270447336011101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308098707026846964890674067 462148060540270447336011101)
        ·
          refine ⟨173305522702601417751004163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462148060540270447336011101 173305522702601417751004163)
          ·
            refine ⟨259958284053902126626506245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173305522702601417751004163 259958284053902126626506245)
            ·
              refine ⟨48742178260106648742469921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259958284053902126626506245 48742178260106648742469921)
              ·
                refine ⟨36556633695079986556852441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48742178260106648742469921 36556633695079986556852441)
                ·
                  refine ⟨27417475271309989917639331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36556633695079986556852441 27417475271309989917639331)
                  ·
                    refine ⟨41126212906964984876458997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27417475271309989917639331 41126212906964984876458997)
                    ·
                      refine ⟨3855582460027967332168031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41126212906964984876458997 3855582460027967332168031)
                      ·
                        rfl

theorem cell23_7508720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_7508720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508720 prefixEnd_7508720 := by exact prefixLift 7508720
  have htrace : WordTrace (prefixWord ++ tailWord_7508720) baseStart_7508720 baseEnd_7508720 := by
    simpa [prefixWord, tailWord_7508720, baseEnd_7508720] using wordTrace_append hprefix tailTrace_7508720
  have hstable : (prefixWord ++ tailWord_7508720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508720).length < 2 ^ (prefixWord ++ tailWord_7508720).sum := by decide
  have hdescent : baseEnd_7508720 < baseStart_7508720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508730 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_7508730 : Nat := 118140960795 + 7508730 * 2 ^ 59
def prefixEnd_7508730 : Nat := 4983230072969 + 3 ^ 40 * 7508730 * 2
def baseEnd_7508730 : Nat := 3855587594834512293042985

theorem tailTrace_7508730 : CollatzResearch.WordTrace tailWord_7508730 prefixEnd_7508730 3855587594834512293042985 := by
  unfold tailWord_7508730
  simp only [CollatzResearch.WordTrace]
  refine ⟨68466470521790268458226911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182577254724774049221938429 68466470521790268458226911)
  ·
    refine ⟨102699705782685402687340367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68466470521790268458226911 102699705782685402687340367)
    ·
      refine ⟨154049558674028104031010551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102699705782685402687340367 154049558674028104031010551)
      ·
        refine ⟨231074338011042156046515827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154049558674028104031010551 231074338011042156046515827)
        ·
          refine ⟨346611507016563234069773741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231074338011042156046515827 346611507016563234069773741)
          ·
            refine ⟨129979315131211212776165153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346611507016563234069773741 129979315131211212776165153)
            ·
              refine ⟨97484486348408409582123865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129979315131211212776165153 97484486348408409582123865)
              ·
                refine ⟨73113364761306307186592899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97484486348408409582123865 73113364761306307186592899)
                ·
                  refine ⟨109670047141959460779889349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73113364761306307186592899 109670047141959460779889349)
                  ·
                    refine ⟨20563133839117398896229253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109670047141959460779889349 20563133839117398896229253)
                    ·
                      refine ⟨3855587594834512293042985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20563133839117398896229253 3855587594834512293042985)
                      ·
                        rfl

theorem cell23_7508730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_7508730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508730 prefixEnd_7508730 := by exact prefixLift 7508730
  have htrace : WordTrace (prefixWord ++ tailWord_7508730) baseStart_7508730 baseEnd_7508730 := by
    simpa [prefixWord, tailWord_7508730, baseEnd_7508730] using wordTrace_append hprefix tailTrace_7508730
  have hstable : (prefixWord ++ tailWord_7508730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508730).length < 2 ^ (prefixWord ++ tailWord_7508730).sum := by decide
  have hdescent : baseEnd_7508730 < baseStart_7508730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508750 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7508750 : Nat := 118140960795 + 7508750 * 2 ^ 59
def prefixEnd_7508750 : Nat := 4983230072969 + 3 ^ 40 * 7508750 * 2
def baseEnd_7508750 : Nat := 3855597864447602214792893

theorem tailTrace_7508750 : CollatzResearch.WordTrace tailWord_7508750 prefixEnd_7508750 3855597864447602214792893 := by
  unfold tailWord_7508750
  simp only [CollatzResearch.WordTrace]
  refine ⟨34233326443386077156079463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182577741031392411499090469 34233326443386077156079463)
  ·
    refine ⟨51349989665079115734119195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34233326443386077156079463 51349989665079115734119195)
    ·
      refine ⟨77024984497618673601178793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51349989665079115734119195 77024984497618673601178793)
      ·
        refine ⟨57768738373214005200884095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77024984497618673601178793 57768738373214005200884095)
        ·
          refine ⟨86653107559821007801326143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57768738373214005200884095 86653107559821007801326143)
          ·
            refine ⟨129979661339731511701989215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86653107559821007801326143 129979661339731511701989215)
            ·
              refine ⟨194969492009597267552983823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129979661339731511701989215 194969492009597267552983823)
              ·
                refine ⟨292454238014395901329475735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194969492009597267552983823 292454238014395901329475735)
                ·
                  refine ⟨438681357021593851994213603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292454238014395901329475735 438681357021593851994213603)
                  ·
                    refine ⟨658022035532390777991320405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 438681357021593851994213603 658022035532390777991320405)
                    ·
                      refine ⟨3855597864447602214792893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 658022035532390777991320405 3855597864447602214792893)
                      ·
                        rfl

theorem cell23_7508750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7508750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508750 prefixEnd_7508750 := by exact prefixLift 7508750
  have htrace : WordTrace (prefixWord ++ tailWord_7508750) baseStart_7508750 baseEnd_7508750 := by
    simpa [prefixWord, tailWord_7508750, baseEnd_7508750] using wordTrace_append hprefix tailTrace_7508750
  have hstable : (prefixWord ++ tailWord_7508750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508750).length < 2 ^ (prefixWord ++ tailWord_7508750).sum := by decide
  have hdescent : baseEnd_7508750 < baseStart_7508750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508768 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 2, 2, 2]
def baseStart_7508768 : Nat := 118140960795 + 7508768 * 2 ^ 59
def prefixEnd_7508768 : Nat := 4983230072969 + 3 ^ 40 * 7508768 * 2
def baseEnd_7508768 : Nat := 3855607107099383144367811

theorem tailTrace_7508768 : CollatzResearch.WordTrace tailWord_7508768 prefixEnd_7508768 3855607107099383144367811 := by
  unfold tailWord_7508768
  simp only [CollatzResearch.WordTrace]
  refine ⟨136933634030511703161395479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182578178707348937548527305 136933634030511703161395479)
  ·
    refine ⟨205400451045767554742093219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136933634030511703161395479 205400451045767554742093219)
    ·
      refine ⟨308100676568651332113139829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205400451045767554742093219 308100676568651332113139829)
      ·
        refine ⟨28884438428311062385606859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308100676568651332113139829 28884438428311062385606859)
        ·
          refine ⟨43326657642466593578410289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28884438428311062385606859 43326657642466593578410289)
          ·
            refine ⟨32494993231849945183807717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43326657642466593578410289 32494993231849945183807717)
            ·
              refine ⟨6092811230971864721963947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32494993231849945183807717 6092811230971864721963947)
              ·
                refine ⟨9139216846457797082945921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092811230971864721963947 9139216846457797082945921)
                ·
                  refine ⟨6854412634843347812209441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9139216846457797082945921 6854412634843347812209441)
                  ·
                    refine ⟨5140809476132510859157081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6854412634843347812209441 5140809476132510859157081)
                    ·
                      refine ⟨3855607107099383144367811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140809476132510859157081 3855607107099383144367811)
                      ·
                        rfl

theorem cell23_7508768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_7508768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508768 prefixEnd_7508768 := by exact prefixLift 7508768
  have htrace : WordTrace (prefixWord ++ tailWord_7508768) baseStart_7508768 baseEnd_7508768 := by
    simpa [prefixWord, tailWord_7508768, baseEnd_7508768] using wordTrace_append hprefix tailTrace_7508768
  have hstable : (prefixWord ++ tailWord_7508768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508768).length < 2 ^ (prefixWord ++ tailWord_7508768).sum := by decide
  have hdescent : baseEnd_7508768 < baseStart_7508768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508777 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 2, 5, 2]
def baseStart_7508777 : Nat := 118140960795 + 7508777 * 2 ^ 59
def prefixEnd_7508777 : Nat := 4983230072969 + 3 ^ 40 * 7508777 * 2
def baseEnd_7508777 : Nat := 3855611728425273609155269

theorem tailTrace_7508777 : CollatzResearch.WordTrace tailWord_7508777 prefixEnd_7508777 3855611728425273609155269 := by
  unfold tailWord_7508777
  simp only [CollatzResearch.WordTrace]
  refine ⟨273867596317990800859868585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182578397545327200573245723 273867596317990800859868585)
  ·
    refine ⟨205400697238493100644901439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273867596317990800859868585 205400697238493100644901439)
    ·
      refine ⟨308101045857739650967352159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205400697238493100644901439 308101045857739650967352159)
      ·
        refine ⟨462151568786609476451028239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308101045857739650967352159 462151568786609476451028239)
        ·
          refine ⟨693227353179914214676542359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462151568786609476451028239 693227353179914214676542359)
          ·
            refine ⟨1039841029769871322014813539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693227353179914214676542359 1039841029769871322014813539)
            ·
              refine ⟨1559761544654806983022220309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039841029769871322014813539 1559761544654806983022220309)
              ·
                refine ⟨73113822405694077329166577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1559761544654806983022220309 73113822405694077329166577)
                ·
                  refine ⟨54835366804270557996874933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73113822405694077329166577 54835366804270557996874933)
                  ·
                    refine ⟨5140815637900364812207025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54835366804270557996874933 5140815637900364812207025)
                    ·
                      refine ⟨3855611728425273609155269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140815637900364812207025 3855611728425273609155269)
                      ·
                        rfl

theorem cell23_7508777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 5, 2].length) (baseStart_7508777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508777 prefixEnd_7508777 := by exact prefixLift 7508777
  have htrace : WordTrace (prefixWord ++ tailWord_7508777) baseStart_7508777 baseEnd_7508777 := by
    simpa [prefixWord, tailWord_7508777, baseEnd_7508777] using wordTrace_append hprefix tailTrace_7508777
  have hstable : (prefixWord ++ tailWord_7508777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508777).length < 2 ^ (prefixWord ++ tailWord_7508777).sum := by decide
  have hdescent : baseEnd_7508777 < baseStart_7508777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508780 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_7508780 : Nat := 118140960795 + 7508780 * 2 ^ 59
def prefixEnd_7508780 : Nat := 4983230072969 + 3 ^ 40 * 7508780 * 2
def baseEnd_7508780 : Nat := 3855613268867237097417755

theorem tailTrace_7508780 : CollatzResearch.WordTrace tailWord_7508780 prefixEnd_7508780 3855613268867237097417755 := by
  unfold tailWord_7508780
  simp only [CollatzResearch.WordTrace]
  refine ⟨136933852868489966186113897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182578470491319954914818529 136933852868489966186113897)
  ·
    refine ⟨102700389651367474639585423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136933852868489966186113897 102700389651367474639585423)
    ·
      refine ⟨154050584477051211959378135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102700389651367474639585423 154050584477051211959378135)
      ·
        refine ⟨231075876715576817939067203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154050584477051211959378135 231075876715576817939067203)
        ·
          refine ⟨346613815073365226908600805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231075876715576817939067203 346613815073365226908600805)
          ·
            refine ⟨64990090326255980045362651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346613815073365226908600805 64990090326255980045362651)
            ·
              refine ⟨97485135489383970068043977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64990090326255980045362651 97485135489383970068043977)
              ·
                refine ⟨73113851617037977551032983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97485135489383970068043977 73113851617037977551032983)
                ·
                  refine ⟨109670777425556966326549475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73113851617037977551032983 109670777425556966326549475)
                  ·
                    refine ⟨164506166138335449489824213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109670777425556966326549475 164506166138335449489824213)
                    ·
                      refine ⟨3855613268867237097417755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164506166138335449489824213 3855613268867237097417755)
                      ·
                        rfl

theorem cell23_7508780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_7508780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508780 prefixEnd_7508780 := by exact prefixLift 7508780
  have htrace : WordTrace (prefixWord ++ tailWord_7508780) baseStart_7508780 baseEnd_7508780 := by
    simpa [prefixWord, tailWord_7508780, baseEnd_7508780] using wordTrace_append hprefix tailTrace_7508780
  have hstable : (prefixWord ++ tailWord_7508780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508780).length < 2 ^ (prefixWord ++ tailWord_7508780).sum := by decide
  have hdescent : baseEnd_7508780 < baseStart_7508780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508787 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 2, 5]
def baseStart_7508787 : Nat := 118140960795 + 7508787 * 2 ^ 59
def prefixEnd_7508787 : Nat := 4983230072969 + 3 ^ 40 * 7508787 * 2
def baseEnd_7508787 : Nat := 1285205621077272856676741

theorem tailTrace_7508787 : CollatzResearch.WordTrace tailWord_7508787 prefixEnd_7508787 1285205621077272856676741 := by
  unfold tailWord_7508787
  simp only [CollatzResearch.WordTrace]
  refine ⟨273867961047954572567732615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182578640698636381711821743 273867961047954572567732615)
  ·
    refine ⟨410801941571931858851598923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273867961047954572567732615 410801941571931858851598923)
    ·
      refine ⟨616202912357897788277398385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410801941571931858851598923 616202912357897788277398385)
      ·
        refine ⟨462152184268423341208048789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616202912357897788277398385 462152184268423341208048789)
        ·
          refine ⟨21663383637582344119127287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 462152184268423341208048789 21663383637582344119127287)
          ·
            refine ⟨32495075456373516178690931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21663383637582344119127287 32495075456373516178690931)
            ·
              refine ⟨48742613184560274268036397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32495075456373516178690931 48742613184560274268036397)
              ·
                refine ⟨18278479944210102850513649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48742613184560274268036397 18278479944210102850513649)
                ·
                  refine ⟨13708859958157577137885237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18278479944210102850513649 13708859958157577137885237)
                  ·
                    refine ⟨1285205621077272856676741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13708859958157577137885237 1285205621077272856676741)
                    ·
                      rfl

theorem cell23_7508787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 5].length) (baseStart_7508787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508787 prefixEnd_7508787 := by exact prefixLift 7508787
  have htrace : WordTrace (prefixWord ++ tailWord_7508787) baseStart_7508787 baseEnd_7508787 := by
    simpa [prefixWord, tailWord_7508787, baseEnd_7508787] using wordTrace_append hprefix tailTrace_7508787
  have hstable : (prefixWord ++ tailWord_7508787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508787).length < 2 ^ (prefixWord ++ tailWord_7508787).sum := by decide
  have hdescent : baseEnd_7508787 < baseStart_7508787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508854 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7508854 : Nat := 118140960795 + 7508854 * 2 ^ 59
def prefixEnd_7508854 : Nat := 4983230072969 + 3 ^ 40 * 7508854 * 2
def baseEnd_7508854 : Nat := 3855651266435669807892415

theorem tailTrace_7508854 : CollatzResearch.WordTrace tailWord_7508854 prefixEnd_7508854 3855651266435669807892415 := by
  unfold tailWord_7508854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17116900296169490188151351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182580269825807895340281077 17116900296169490188151351)
  ·
    refine ⟨25675350444254235282227027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17116900296169490188151351 25675350444254235282227027)
    ·
      refine ⟨38513025666381352923340541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25675350444254235282227027 38513025666381352923340541)
      ·
        refine ⟨14442384624893007346252703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38513025666381352923340541 14442384624893007346252703)
        ·
          refine ⟨21663576937339511019379055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14442384624893007346252703 21663576937339511019379055)
          ·
            refine ⟨32495365406009266529068583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21663576937339511019379055 32495365406009266529068583)
            ·
              refine ⟨48743048109013899793602875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32495365406009266529068583 48743048109013899793602875)
              ·
                refine ⟨73114572163520849690404313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48743048109013899793602875 73114572163520849690404313)
                ·
                  refine ⟨54835929122640637267803235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73114572163520849690404313 54835929122640637267803235)
                  ·
                    refine ⟨82253893683960955901704853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54835929122640637267803235 82253893683960955901704853)
                    ·
                      refine ⟨3855651266435669807892415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82253893683960955901704853 3855651266435669807892415)
                      ·
                        rfl

theorem cell23_7508854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7508854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508854 prefixEnd_7508854 := by exact prefixLift 7508854
  have htrace : WordTrace (prefixWord ++ tailWord_7508854) baseStart_7508854 baseEnd_7508854 := by
    simpa [prefixWord, tailWord_7508854, baseEnd_7508854] using wordTrace_append hprefix tailTrace_7508854
  have hstable : (prefixWord ++ tailWord_7508854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508854).length < 2 ^ (prefixWord ++ tailWord_7508854).sum := by decide
  have hdescent : baseEnd_7508854 < baseStart_7508854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508925 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 3, 1, 3]
def baseStart_7508925 : Nat := 118140960795 + 7508925 * 2 ^ 59
def prefixEnd_7508925 : Nat := 4983230072969 + 3 ^ 40 * 7508925 * 2
def baseEnd_7508925 : Nat := 3855687723562139030104589

theorem tailTrace_7508925 : CollatzResearch.WordTrace tailWord_7508925 prefixEnd_7508925 3855687723562139030104589 := by
  unfold tailWord_7508925
  simp only [CollatzResearch.WordTrace]
  refine ⟨273872994321454622136256229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182581996214303081424170819 273872994321454622136256229)
  ·
    refine ⟨51351186435272741650548043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273872994321454622136256229 51351186435272741650548043)
    ·
      refine ⟨77026779652909112475822065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51351186435272741650548043 77026779652909112475822065)
      ·
        refine ⟨57770084739681834356866549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77026779652909112475822065 57770084739681834356866549)
        ·
          refine ⟨5415945444345171970956239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57770084739681834356866549 5415945444345171970956239)
          ·
            refine ⟨8123918166517757956434359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415945444345171970956239 8123918166517757956434359)
            ·
              refine ⟨12185877249776636934651539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123918166517757956434359 12185877249776636934651539)
              ·
                refine ⟨18278815874664955401977309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12185877249776636934651539 18278815874664955401977309)
                ·
                  refine ⟨6854555952999358275741491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18278815874664955401977309 6854555952999358275741491)
                  ·
                    refine ⟨10281833929499037413612237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6854555952999358275741491 10281833929499037413612237)
                    ·
                      refine ⟨3855687723562139030104589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10281833929499037413612237 3855687723562139030104589)
                      ·
                        rfl

theorem cell23_7508925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_7508925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508925 prefixEnd_7508925 := by exact prefixLift 7508925
  have htrace : WordTrace (prefixWord ++ tailWord_7508925) baseStart_7508925 baseEnd_7508925 := by
    simpa [prefixWord, tailWord_7508925, baseEnd_7508925] using wordTrace_append hprefix tailTrace_7508925
  have hstable : (prefixWord ++ tailWord_7508925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508925).length < 2 ^ (prefixWord ++ tailWord_7508925).sum := by decide
  have hdescent : baseEnd_7508925 < baseStart_7508925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508927 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_7508927 : Nat := 118140960795 + 7508927 * 2 ^ 59
def prefixEnd_7508927 : Nat := 4983230072969 + 3 ^ 40 * 7508927 * 2
def baseEnd_7508927 : Nat := 3855688750523448022279579

theorem tailTrace_7508927 : CollatzResearch.WordTrace tailWord_7508927 prefixEnd_7508927 3855688750523448022279579 := by
  unfold tailWord_7508927
  simp only [CollatzResearch.WordTrace]
  refine ⟨273873067267447376477829035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182582044844964917651886023 273873067267447376477829035)
  ·
    refine ⟨410809600901171064716743553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273873067267447376477829035 410809600901171064716743553)
    ·
      refine ⟨308107200675878298537557665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410809600901171064716743553 308107200675878298537557665)
      ·
        refine ⟨231080400506908723903168249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308107200675878298537557665 231080400506908723903168249)
        ·
          refine ⟨173310300380181542927376187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231080400506908723903168249 173310300380181542927376187)
          ·
            refine ⟨259965450570272314391064281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173310300380181542927376187 259965450570272314391064281)
            ·
              refine ⟨194974087927704235793298211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259965450570272314391064281 194974087927704235793298211)
              ·
                refine ⟨292461131891556353689947317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194974087927704235793298211 292461131891556353689947317)
                ·
                  refine ⟨27418231114833408158432561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292461131891556353689947317 27418231114833408158432561)
                  ·
                    refine ⟨20563673336125056118824421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27418231114833408158432561 20563673336125056118824421)
                    ·
                      refine ⟨3855688750523448022279579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20563673336125056118824421 3855688750523448022279579)
                      ·
                        rfl

theorem cell23_7508927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_7508927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508927 prefixEnd_7508927 := by exact prefixLift 7508927
  have htrace : WordTrace (prefixWord ++ tailWord_7508927) baseStart_7508927 baseEnd_7508927 := by
    simpa [prefixWord, tailWord_7508927, baseEnd_7508927] using wordTrace_append hprefix tailTrace_7508927
  have hstable : (prefixWord ++ tailWord_7508927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508927).length < 2 ^ (prefixWord ++ tailWord_7508927).sum := by decide
  have hdescent : baseEnd_7508927 < baseStart_7508927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508948 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_7508948 : Nat := 118140960795 + 7508948 * 2 ^ 59
def prefixEnd_7508948 : Nat := 4983230072969 + 3 ^ 40 * 7508948 * 2
def baseEnd_7508948 : Nat := 3855699533617192440116983

theorem tailTrace_7508948 : CollatzResearch.WordTrace tailWord_7508948 prefixEnd_7508948 3855699533617192440116983 := by
  unfold tailWord_7508948
  simp only [CollatzResearch.WordTrace]
  refine ⟨136936916600185648532171749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182582555466914198042895665 136936916600185648532171749)
  ·
    refine ⟨25675671862534809099782203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136936916600185648532171749 25675671862534809099782203)
    ·
      refine ⟨38513507793802213649673305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25675671862534809099782203 38513507793802213649673305)
      ·
        refine ⟨28885130845351660237254979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38513507793802213649673305 28885130845351660237254979)
        ·
          refine ⟨43327696268027490355882469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28885130845351660237254979 43327696268027490355882469)
          ·
            refine ⟨8123943050255154441727963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43327696268027490355882469 8123943050255154441727963)
            ·
              refine ⟨12185914575382731662591945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123943050255154441727963 12185914575382731662591945)
              ·
                refine ⟨9139435931537048746943959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12185914575382731662591945 9139435931537048746943959)
                ·
                  refine ⟨13709153897305573120415939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9139435931537048746943959 13709153897305573120415939)
                  ·
                    refine ⟨20563730845958359680623909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13709153897305573120415939 20563730845958359680623909)
                    ·
                      refine ⟨3855699533617192440116983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20563730845958359680623909 3855699533617192440116983)
                      ·
                        rfl

theorem cell23_7508948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_7508948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508948 prefixEnd_7508948 := by exact prefixLift 7508948
  have htrace : WordTrace (prefixWord ++ tailWord_7508948) baseStart_7508948 baseEnd_7508948 := by
    simpa [prefixWord, tailWord_7508948, baseEnd_7508948] using wordTrace_append hprefix tailTrace_7508948
  have hstable : (prefixWord ++ tailWord_7508948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508948).length < 2 ^ (prefixWord ++ tailWord_7508948).sum := by decide
  have hdescent : baseEnd_7508948 < baseStart_7508948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508965 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7508965 : Nat := 118140960795 + 7508965 * 2 ^ 59
def prefixEnd_7508965 : Nat := 4983230072969 + 3 ^ 40 * 7508965 * 2
def baseEnd_7508965 : Nat := 3855708262788318873604405

theorem tailTrace_7508965 : CollatzResearch.WordTrace tailWord_7508965 prefixEnd_7508965 3855708262788318873604405 := by
  unfold tailWord_7508965
  simp only [CollatzResearch.WordTrace]
  refine ⟨273874453241309708967712349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182582968827539805978474899 273874453241309708967712349)
  ·
    refine ⟨102702919965491140862892131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273874453241309708967712349 102702919965491140862892131)
    ·
      refine ⟨154054379948236711294338197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102702919965491140862892131 154054379948236711294338197)
      ·
        refine ⟨7221299060073595841922103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154054379948236711294338197 7221299060073595841922103)
        ·
          refine ⟨10831948590110393762883155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7221299060073595841922103 10831948590110393762883155)
          ·
            refine ⟨16247922885165590644324733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10831948590110393762883155 16247922885165590644324733)
            ·
              refine ⟨6092971081937096491621775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16247922885165590644324733 6092971081937096491621775)
              ·
                refine ⟨9139456622905644737432663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092971081937096491621775 9139456622905644737432663)
                ·
                  refine ⟨13709184934358467106148995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9139456622905644737432663 13709184934358467106148995)
                  ·
                    refine ⟨20563777401537700659223493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13709184934358467106148995 20563777401537700659223493)
                    ·
                      refine ⟨3855708262788318873604405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20563777401537700659223493 3855708262788318873604405)
                      ·
                        rfl

theorem cell23_7508965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7508965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508965 prefixEnd_7508965 := by exact prefixLift 7508965
  have htrace : WordTrace (prefixWord ++ tailWord_7508965) baseStart_7508965 baseEnd_7508965 := by
    simpa [prefixWord, tailWord_7508965, baseEnd_7508965] using wordTrace_append hprefix tailTrace_7508965
  have hstable : (prefixWord ++ tailWord_7508965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508965).length < 2 ^ (prefixWord ++ tailWord_7508965).sum := by decide
  have hdescent : baseEnd_7508965 < baseStart_7508965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7508982 : List Nat := [5, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_7508982 : Nat := 118140960795 + 7508982 * 2 ^ 59
def prefixEnd_7508982 : Nat := 4983230072969 + 3 ^ 40 * 7508982 * 2
def baseEnd_7508982 : Nat := 3855716991959445307091827

theorem tailTrace_7508982 : CollatzResearch.WordTrace tailWord_7508982 prefixEnd_7508982 3855716991959445307091827 := by
  unfold tailWord_7508982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17117192080140507554442575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182583382188165413914054133 17117192080140507554442575)
  ·
    refine ⟨25675788120210761331663863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17117192080140507554442575 25675788120210761331663863)
    ·
      refine ⟨38513682180316141997495795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25675788120210761331663863 38513682180316141997495795)
      ·
        refine ⟨57770523270474212996243693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38513682180316141997495795 57770523270474212996243693)
        ·
          refine ⟨21663946226427829873591385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57770523270474212996243693 21663946226427829873591385)
          ·
            refine ⟨16247959669820872405193539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21663946226427829873591385 16247959669820872405193539)
            ·
              refine ⟨24371939504731308607790309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16247959669820872405193539 24371939504731308607790309)
              ·
                refine ⟨4569738657137120363960683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24371939504731308607790309 4569738657137120363960683)
                ·
                  refine ⟨6854607985705680545941025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569738657137120363960683 6854607985705680545941025)
                  ·
                    refine ⟨5140955989279260409455769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6854607985705680545941025 5140955989279260409455769)
                    ·
                      refine ⟨3855716991959445307091827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140955989279260409455769 3855716991959445307091827)
                      ·
                        rfl

theorem cell23_7508982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_7508982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7508982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7508982 prefixEnd_7508982 := by exact prefixLift 7508982
  have htrace : WordTrace (prefixWord ++ tailWord_7508982) baseStart_7508982 baseEnd_7508982 := by
    simpa [prefixWord, tailWord_7508982, baseEnd_7508982] using wordTrace_append hprefix tailTrace_7508982
  have hstable : (prefixWord ++ tailWord_7508982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7508982).length < 2 ^ (prefixWord ++ tailWord_7508982).sum := by decide
  have hdescent : baseEnd_7508982 < baseStart_7508982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7508982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509007 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_7509007 : Nat := 118140960795 + 7509007 * 2 ^ 59
def prefixEnd_7509007 : Nat := 4983230072969 + 3 ^ 40 * 7509007 * 2
def baseEnd_7509007 : Nat := 3855729828975807709279211

theorem tailTrace_7509007 : CollatzResearch.WordTrace tailWord_7509007 prefixEnd_7509007 3855729828975807709279211 := by
  unfold tailWord_7509007
  simp only [CollatzResearch.WordTrace]
  refine ⟨273875985107157550140741275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182583990071438366760494183 273875985107157550140741275)
  ·
    refine ⟨410813977660736325211111913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273875985107157550140741275 410813977660736325211111913)
    ·
      refine ⟨308110483245552243908333935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410813977660736325211111913 308110483245552243908333935)
      ·
        refine ⟨462165724868328365862500903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308110483245552243908333935 462165724868328365862500903)
        ·
          refine ⟨693248587302492548793751355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462165724868328365862500903 693248587302492548793751355)
          ·
            refine ⟨1039872880953738823190627033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693248587302492548793751355 1039872880953738823190627033)
            ·
              refine ⟨779904660715304117392970275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1039872880953738823190627033 779904660715304117392970275)
              ·
                refine ⟨1169856991072956176089455413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779904660715304117392970275 1169856991072956176089455413)
                ·
                  refine ⟨109674092913089641508386445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1169856991072956176089455413 109674092913089641508386445)
                  ·
                    refine ⟨41127784842408615565644917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109674092913089641508386445 41127784842408615565644917)
                    ·
                      refine ⟨3855729828975807709279211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41127784842408615565644917 3855729828975807709279211)
                      ·
                        rfl

theorem cell23_7509007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_7509007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509007 prefixEnd_7509007 := by exact prefixLift 7509007
  have htrace : WordTrace (prefixWord ++ tailWord_7509007) baseStart_7509007 baseEnd_7509007 := by
    simpa [prefixWord, tailWord_7509007, baseEnd_7509007] using wordTrace_append hprefix tailTrace_7509007
  have hstable : (prefixWord ++ tailWord_7509007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509007).length < 2 ^ (prefixWord ++ tailWord_7509007).sum := by decide
  have hdescent : baseEnd_7509007 < baseStart_7509007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509025 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_7509025 : Nat := 118140960795 + 7509025 * 2 ^ 59
def prefixEnd_7509025 : Nat := 4983230072969 + 3 ^ 40 * 7509025 * 2
def baseEnd_7509025 : Nat := 3855739071627588638854129

theorem tailTrace_7509025 : CollatzResearch.WordTrace tailWord_7509025 prefixEnd_7509025 3855739071627588638854129 := by
  unfold tailWord_7509025
  simp only [CollatzResearch.WordTrace]
  refine ⟨273876641621092339214896529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182584427747394892809931019 273876641621092339214896529)
  ·
    refine ⟨205407481215819254411172397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273876641621092339214896529 205407481215819254411172397)
    ·
      refine ⟨77027805455932220404189649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205407481215819254411172397 77027805455932220404189649)
      ·
        refine ⟨57770854091949165303142237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77027805455932220404189649 57770854091949165303142237)
        ·
          refine ⟨21664070284480936988678339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57770854091949165303142237 21664070284480936988678339)
          ·
            refine ⟨32496105426721405483017509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21664070284480936988678339 32496105426721405483017509)
            ·
              refine ⟨6093019767510263528065783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32496105426721405483017509 6093019767510263528065783)
              ·
                refine ⟨9139529651265395292098675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093019767510263528065783 9139529651265395292098675)
                ·
                  refine ⟨13709294476898092938148013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9139529651265395292098675 13709294476898092938148013)
                  ·
                    refine ⟨5140985428836784851805505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13709294476898092938148013 5140985428836784851805505)
                    ·
                      refine ⟨3855739071627588638854129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5140985428836784851805505 3855739071627588638854129)
                      ·
                        rfl

theorem cell23_7509025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_7509025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509025 prefixEnd_7509025 := by exact prefixLift 7509025
  have htrace : WordTrace (prefixWord ++ tailWord_7509025) baseStart_7509025 baseEnd_7509025 := by
    simpa [prefixWord, tailWord_7509025, baseEnd_7509025] using wordTrace_append hprefix tailTrace_7509025
  have hstable : (prefixWord ++ tailWord_7509025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509025).length < 2 ^ (prefixWord ++ tailWord_7509025).sum := by decide
  have hdescent : baseEnd_7509025 < baseStart_7509025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509031 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7509031 : Nat := 118140960795 + 7509031 * 2 ^ 59
def prefixEnd_7509031 : Nat := 4983230072969 + 3 ^ 40 * 7509031 * 2
def baseEnd_7509031 : Nat := 1285247384170505205126367

theorem tailTrace_7509031 : CollatzResearch.WordTrace tailWord_7509031 prefixEnd_7509031 1285247384170505205126367 := by
  unfold tailWord_7509031
  simp only [CollatzResearch.WordTrace]
  refine ⟨273876860459070602239614947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182584573639380401493076631 273876860459070602239614947)
  ·
    refine ⟨410815290688605903359422421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273876860459070602239614947 410815290688605903359422421)
    ·
      refine ⟨9628483375514200859986463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 410815290688605903359422421 9628483375514200859986463)
      ·
        refine ⟨14442725063271301289979695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9628483375514200859986463 14442725063271301289979695)
        ·
          refine ⟨21664087594906951934969543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14442725063271301289979695 21664087594906951934969543)
          ·
            refine ⟨32496131392360427902454315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21664087594906951934969543 32496131392360427902454315)
            ·
              refine ⟨48744197088540641853681473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32496131392360427902454315 48744197088540641853681473)
              ·
                refine ⟨36558147816405481390261105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48744197088540641853681473 36558147816405481390261105)
                ·
                  refine ⟨27418610862304111042695829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36558147816405481390261105 27418610862304111042695829)
                  ·
                    refine ⟨1285247384170505205126367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27418610862304111042695829 1285247384170505205126367)
                    ·
                      rfl

theorem cell23_7509031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7509031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509031 prefixEnd_7509031 := by exact prefixLift 7509031
  have htrace : WordTrace (prefixWord ++ tailWord_7509031) baseStart_7509031 baseEnd_7509031 := by
    simpa [prefixWord, tailWord_7509031, baseEnd_7509031] using wordTrace_append hprefix tailTrace_7509031
  have hstable : (prefixWord ++ tailWord_7509031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509031).length < 2 ^ (prefixWord ++ tailWord_7509031).sum := by decide
  have hdescent : baseEnd_7509031 < baseStart_7509031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509101 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_7509101 : Nat := 118140960795 + 7509101 * 2 ^ 59
def prefixEnd_7509101 : Nat := 4983230072969 + 3 ^ 40 * 7509101 * 2
def baseEnd_7509101 : Nat := 3855778096157330341503779

theorem tailTrace_7509101 : CollatzResearch.WordTrace tailWord_7509101 prefixEnd_7509101 3855778096157330341503779 := by
  unfold tailWord_7509101
  simp only [CollatzResearch.WordTrace]
  refine ⟨273879413568817004194663157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182586275712544669463108771 273879413568817004194663157)
  ·
    refine ⟨25676195022076594143249671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273879413568817004194663157 25676195022076594143249671)
    ·
      refine ⟨38514292533114891214874507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25676195022076594143249671 38514292533114891214874507)
      ·
        refine ⟨57771438799672336822311761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38514292533114891214874507 57771438799672336822311761)
        ·
          refine ⟨43328579099754252616733821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57771438799672336822311761 43328579099754252616733821)
          ·
            refine ⟨16248217162407844731275183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43328579099754252616733821 16248217162407844731275183)
            ·
              refine ⟨24372325743611767096912775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16248217162407844731275183 24372325743611767096912775)
              ·
                refine ⟨36558488615417650645369163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24372325743611767096912775 36558488615417650645369163)
                ·
                  refine ⟨54837732923126475968053745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36558488615417650645369163 54837732923126475968053745)
                  ·
                    refine ⟨41128299692344856976040309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54837732923126475968053745 41128299692344856976040309)
                    ·
                      refine ⟨3855778096157330341503779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41128299692344856976040309 3855778096157330341503779)
                      ·
                        rfl

theorem cell23_7509101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_7509101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509101 prefixEnd_7509101 := by exact prefixLift 7509101
  have htrace : WordTrace (prefixWord ++ tailWord_7509101) baseStart_7509101 baseEnd_7509101 := by
    simpa [prefixWord, tailWord_7509101, baseEnd_7509101] using wordTrace_append hprefix tailTrace_7509101
  have hstable : (prefixWord ++ tailWord_7509101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509101).length < 2 ^ (prefixWord ++ tailWord_7509101).sum := by decide
  have hdescent : baseEnd_7509101 < baseStart_7509101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509111 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 1, 6, 2]
def baseStart_7509111 : Nat := 118140960795 + 7509111 * 2 ^ 59
def prefixEnd_7509111 : Nat := 4983230072969 + 3 ^ 40 * 7509111 * 2
def baseEnd_7509111 : Nat := 3855783230963875302378733

theorem tailTrace_7509111 : CollatzResearch.WordTrace tailWord_7509111 prefixEnd_7509111 3855783230963875302378733 := by
  unfold tailWord_7509111
  simp only [CollatzResearch.WordTrace]
  refine ⟨273879778298780775902527187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182586518865853850601684791 273879778298780775902527187)
  ·
    refine ⟨410819667448171163853790781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273879778298780775902527187 410819667448171163853790781)
    ·
      refine ⟨154057375293064186445171543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410819667448171163853790781 154057375293064186445171543)
      ·
        refine ⟨231086062939596279667757315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154057375293064186445171543 231086062939596279667757315)
        ·
          refine ⟨346629094409394419501635973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231086062939596279667757315 346629094409394419501635973)
          ·
            refine ⟨64992955201761453656556745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346629094409394419501635973 64992955201761453656556745)
            ·
              refine ⟨48744716401321090242417559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64992955201761453656556745 48744716401321090242417559)
              ·
                refine ⟨73117074601981635363626339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48744716401321090242417559 73117074601981635363626339)
                ·
                  refine ⟨109675611902972453045439509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73117074601981635363626339 109675611902972453045439509)
                  ·
                    refine ⟨5141044307951833736504977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109675611902972453045439509 5141044307951833736504977)
                    ·
                      refine ⟨3855783230963875302378733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5141044307951833736504977 3855783230963875302378733)
                      ·
                        rfl

theorem cell23_7509111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_7509111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509111 prefixEnd_7509111 := by exact prefixLift 7509111
  have htrace : WordTrace (prefixWord ++ tailWord_7509111) baseStart_7509111 baseEnd_7509111 := by
    simpa [prefixWord, tailWord_7509111, baseEnd_7509111] using wordTrace_append hprefix tailTrace_7509111
  have hstable : (prefixWord ++ tailWord_7509111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509111).length < 2 ^ (prefixWord ++ tailWord_7509111).sum := by decide
  have hdescent : baseEnd_7509111 < baseStart_7509111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509148 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_7509148 : Nat := 118140960795 + 7509148 * 2 ^ 59
def prefixEnd_7509148 : Nat := 4983230072969 + 3 ^ 40 * 7509148 * 2
def baseEnd_7509148 : Nat := 3855802229748091657616063

theorem tailTrace_7509148 : CollatzResearch.WordTrace tailWord_7509148 prefixEnd_7509148 3855802229748091657616063 := by
  unfold tailWord_7509148
  simp only [CollatzResearch.WordTrace]
  refine ⟨136940563899823365610812049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182587418533097820814416065 136940563899823365610812049)
  ·
    refine ⟨102705422924867524208109037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136940563899823365610812049 102705422924867524208109037)
    ·
      refine ⟨38514533596825321578040889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102705422924867524208109037 38514533596825321578040889)
      ·
        refine ⟨28885900197618991183530667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38514533596825321578040889 28885900197618991183530667)
        ·
          refine ⟨43328850296428486775296001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28885900197618991183530667 43328850296428486775296001)
          ·
            refine ⟨32496637722321365081472001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43328850296428486775296001 32496637722321365081472001)
            ·
              refine ⟨24372478291741023811104001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32496637722321365081472001 24372478291741023811104001)
              ·
                refine ⟨18279358718805767858328001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24372478291741023811104001 18279358718805767858328001)
                ·
                  refine ⟨13709519039104325893746001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18279358718805767858328001 13709519039104325893746001)
                  ·
                    refine ⟨10282139279328244420309501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13709519039104325893746001 10282139279328244420309501)
                    ·
                      refine ⟨3855802229748091657616063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10282139279328244420309501 3855802229748091657616063)
                      ·
                        rfl

theorem cell23_7509148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_7509148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509148 prefixEnd_7509148 := by exact prefixLift 7509148
  have htrace : WordTrace (prefixWord ++ tailWord_7509148) baseStart_7509148 baseEnd_7509148 := by
    simpa [prefixWord, tailWord_7509148, baseEnd_7509148] using wordTrace_append hprefix tailTrace_7509148
  have hstable : (prefixWord ++ tailWord_7509148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509148).length < 2 ^ (prefixWord ++ tailWord_7509148).sum := by decide
  have hdescent : baseEnd_7509148 < baseStart_7509148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509181 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_7509181 : Nat := 118140960795 + 7509181 * 2 ^ 59
def prefixEnd_7509181 : Nat := 4983230072969 + 3 ^ 40 * 7509181 * 2
def baseEnd_7509181 : Nat := 1285273058203230009501137

theorem tailTrace_7509181 : CollatzResearch.WordTrace tailWord_7509181 prefixEnd_7509181 1285273058203230009501137 := by
  unfold tailWord_7509181
  simp only [CollatzResearch.WordTrace]
  refine ⟨273882331408527177857575397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182588220939018118571716931 273882331408527177857575397)
  ·
    refine ⟨51352937139098845848295387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273882331408527177857575397 51352937139098845848295387)
    ·
      refine ⟨77029405708648268772443081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51352937139098845848295387 77029405708648268772443081)
      ·
        refine ⟨57772054281486201579332311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77029405708648268772443081 57772054281486201579332311)
        ·
          refine ⟨86658081422229302368998467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57772054281486201579332311 86658081422229302368998467)
          ·
            refine ⟨129987122133343953553497701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86658081422229302368998467 129987122133343953553497701)
            ·
              refine ⟨24372585400001991291280819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129987122133343953553497701 24372585400001991291280819)
              ·
                refine ⟨36558878100002986936921229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24372585400001991291280819 36558878100002986936921229)
                ·
                  refine ⟨13709579287501120101345461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36558878100002986936921229 13709579287501120101345461)
                  ·
                    refine ⟨1285273058203230009501137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13709579287501120101345461 1285273058203230009501137)
                    ·
                      rfl

theorem cell23_7509181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_7509181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509181 prefixEnd_7509181 := by exact prefixLift 7509181
  have htrace : WordTrace (prefixWord ++ tailWord_7509181) baseStart_7509181 baseEnd_7509181 := by
    simpa [prefixWord, tailWord_7509181, baseEnd_7509181] using wordTrace_append hprefix tailTrace_7509181
  have hstable : (prefixWord ++ tailWord_7509181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509181).length < 2 ^ (prefixWord ++ tailWord_7509181).sum := by decide
  have hdescent : baseEnd_7509181 < baseStart_7509181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509228 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_7509228 : Nat := 118140960795 + 7509228 * 2 ^ 59
def prefixEnd_7509228 : Nat := 4983230072969 + 3 ^ 40 * 7509228 * 2
def baseEnd_7509228 : Nat := 1285281102733483781538565

theorem tailTrace_7509228 : CollatzResearch.WordTrace tailWord_7509228 prefixEnd_7509228 1285281102733483781538565 := by
  unfold tailWord_7509228
  simp only [CollatzResearch.WordTrace]
  refine ⟨136942022819678452442268169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182589363759571269923024225 136942022819678452442268169)
  ·
    refine ⟨102706517114758839331701127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136942022819678452442268169 102706517114758839331701127)
    ·
      refine ⟨154059775672138258997551691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102706517114758839331701127 154059775672138258997551691)
      ·
        refine ⟨231089663508207388496327537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154059775672138258997551691 231089663508207388496327537)
        ·
          refine ⟨173317247631155541372245653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231089663508207388496327537 173317247631155541372245653)
          ·
            refine ⟨8124245982710416001824015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173317247631155541372245653 8124245982710416001824015)
            ·
              refine ⟨12186368974065624002736023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124245982710416001824015 12186368974065624002736023)
              ·
                refine ⟨18279553461098436004104035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12186368974065624002736023 18279553461098436004104035)
                ·
                  refine ⟨27419330191647654006156053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18279553461098436004104035 27419330191647654006156053)
                  ·
                    refine ⟨1285281102733483781538565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27419330191647654006156053 1285281102733483781538565)
                    ·
                      rfl

theorem cell23_7509228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_7509228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509228 prefixEnd_7509228 := by exact prefixLift 7509228
  have htrace : WordTrace (prefixWord ++ tailWord_7509228) baseStart_7509228 baseEnd_7509228 := by
    simpa [prefixWord, tailWord_7509228, baseEnd_7509228] using wordTrace_append hprefix tailTrace_7509228
  have hstable : (prefixWord ++ tailWord_7509228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509228).length < 2 ^ (prefixWord ++ tailWord_7509228).sum := by decide
  have hdescent : baseEnd_7509228 < baseStart_7509228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509235 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 3, 2, 2]
def baseStart_7509235 : Nat := 118140960795 + 7509235 * 2 ^ 59
def prefixEnd_7509235 : Nat := 4983230072969 + 3 ^ 40 * 7509235 * 2
def baseEnd_7509235 : Nat := 3855846902565032817228163

theorem tailTrace_7509235 : CollatzResearch.WordTrace tailWord_7509235 prefixEnd_7509235 3855846902565032817228163 := by
  unfold tailWord_7509235
  simp only [CollatzResearch.WordTrace]
  refine ⟨273884300950331545080041159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182589533966887696720027439 273884300950331545080041159)
  ·
    refine ⟨410826451425497317620061739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273884300950331545080041159 410826451425497317620061739)
    ·
      refine ⟨616239677138245976430092609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410826451425497317620061739 616239677138245976430092609)
      ·
        refine ⟨462179757853684482322569457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616239677138245976430092609 462179757853684482322569457)
        ·
          refine ⟨346634818390263361741927093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462179757853684482322569457 346634818390263361741927093)
          ·
            refine ⟨32497014224087190163305665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 346634818390263361741927093 32497014224087190163305665)
            ·
              refine ⟨24372760668065392622479249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32497014224087190163305665 24372760668065392622479249)
              ·
                refine ⟨18279570501049044466859437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24372760668065392622479249 18279570501049044466859437)
                ·
                  refine ⟨6854838937893391675072289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18279570501049044466859437 6854838937893391675072289)
                  ·
                    refine ⟨5141129203420043756304217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6854838937893391675072289 5141129203420043756304217)
                    ·
                      refine ⟨3855846902565032817228163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5141129203420043756304217 3855846902565032817228163)
                      ·
                        rfl

theorem cell23_7509235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 2, 2].length) (baseStart_7509235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509235 prefixEnd_7509235 := by exact prefixLift 7509235
  have htrace : WordTrace (prefixWord ++ tailWord_7509235) baseStart_7509235 baseEnd_7509235 := by
    simpa [prefixWord, tailWord_7509235, baseEnd_7509235] using wordTrace_append hprefix tailTrace_7509235
  have hstable : (prefixWord ++ tailWord_7509235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509235).length < 2 ^ (prefixWord ++ tailWord_7509235).sum := by decide
  have hdescent : baseEnd_7509235 < baseStart_7509235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509271 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 2, 7]
def baseStart_7509271 : Nat := 118140960795 + 7509271 * 2 ^ 59
def prefixEnd_7509271 : Nat := 4983230072969 + 3 ^ 40 * 7509271 * 2
def baseEnd_7509271 : Nat := 1285288462622864892125999

theorem tailTrace_7509271 : CollatzResearch.WordTrace tailWord_7509271 prefixEnd_7509271 1285288462622864892125999 := by
  unfold tailWord_7509271
  simp only [CollatzResearch.WordTrace]
  refine ⟨273885613978201123228351667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182590409318800748818901111 273885613978201123228351667)
  ·
    refine ⟨410828420967301684842527501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273885613978201123228351667 410828420967301684842527501)
    ·
      refine ⟨154060657862738131815947813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410828420967301684842527501 154060657862738131815947813)
      ·
        refine ⟨28886373349263399715490215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154060657862738131815947813 28886373349263399715490215)
        ·
          refine ⟨43329560023895099573235323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28886373349263399715490215 43329560023895099573235323)
          ·
            refine ⟨64994340035842649359852985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43329560023895099573235323 64994340035842649359852985)
            ·
              refine ⟨48745755026881987019889739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64994340035842649359852985 48745755026881987019889739)
              ·
                refine ⟨73118632540322980529834609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48745755026881987019889739 73118632540322980529834609)
                ·
                  refine ⟨54838974405242235397375957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73118632540322980529834609 54838974405242235397375957)
                  ·
                    refine ⟨1285288462622864892125999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54838974405242235397375957 1285288462622864892125999)
                    ·
                      rfl

theorem cell23_7509271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_7509271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509271 prefixEnd_7509271 := by exact prefixLift 7509271
  have htrace : WordTrace (prefixWord ++ tailWord_7509271) baseStart_7509271 baseEnd_7509271 := by
    simpa [prefixWord, tailWord_7509271, baseEnd_7509271] using wordTrace_append hprefix tailTrace_7509271
  have hstable : (prefixWord ++ tailWord_7509271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509271).length < 2 ^ (prefixWord ++ tailWord_7509271).sum := by decide
  have hdescent : baseEnd_7509271 < baseStart_7509271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509279 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 2, 4]
def baseStart_7509279 : Nat := 118140960795 + 7509279 * 2 ^ 59
def prefixEnd_7509279 : Nat := 4983230072969 + 3 ^ 40 * 7509279 * 2
def baseEnd_7509279 : Nat := 1285289831904610215025987

theorem tailTrace_7509279 : CollatzResearch.WordTrace tailWord_7509279 prefixEnd_7509279 1285289831904610215025987 := by
  unfold tailWord_7509279
  simp only [CollatzResearch.WordTrace]
  refine ⟨273885905762172140594642891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182590603841448093729761927 273885905762172140594642891)
  ·
    refine ⟨410828858643258210891964337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273885905762172140594642891 410828858643258210891964337)
    ·
      refine ⟨308121643982443658168973253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410828858643258210891964337 308121643982443658168973253)
      ·
        refine ⟨57772808246708185906682485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308121643982443658168973253 57772808246708185906682485)
        ·
          refine ⟨5416200773128892428751483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57772808246708185906682485 5416200773128892428751483)
          ·
            refine ⟨8124301159693338643127225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416200773128892428751483 8124301159693338643127225)
            ·
              refine ⟨6093225869770003982345419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8124301159693338643127225 6093225869770003982345419)
              ·
                refine ⟨9139838804655005973518129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093225869770003982345419 9139838804655005973518129)
                ·
                  refine ⟨6854879103491254480138597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9139838804655005973518129 6854879103491254480138597)
                  ·
                    refine ⟨1285289831904610215025987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854879103491254480138597 1285289831904610215025987)
                    ·
                      rfl

theorem cell23_7509279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 4].length) (baseStart_7509279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509279 prefixEnd_7509279 := by exact prefixLift 7509279
  have htrace : WordTrace (prefixWord ++ tailWord_7509279) baseStart_7509279 baseEnd_7509279 := by
    simpa [prefixWord, tailWord_7509279, baseEnd_7509279] using wordTrace_append hprefix tailTrace_7509279
  have hstable : (prefixWord ++ tailWord_7509279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509279).length < 2 ^ (prefixWord ++ tailWord_7509279).sum := by decide
  have hdescent : baseEnd_7509279 < baseStart_7509279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509312 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 1, 3, 2]
def baseStart_7509312 : Nat := 118140960795 + 7509312 * 2 ^ 59
def prefixEnd_7509312 : Nat := 4983230072969 + 3 ^ 40 * 7509312 * 2
def baseEnd_7509312 : Nat := 3855886440575429015965309

theorem tailTrace_7509312 : CollatzResearch.WordTrace tailWord_7509312 prefixEnd_7509312 3855886440575429015965309 := by
  unfold tailWord_7509312
  simp only [CollatzResearch.WordTrace]
  refine ⟨136943554685526293615297095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182591406247368391487062793 136943554685526293615297095)
  ·
    refine ⟨205415332028289440422945643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136943554685526293615297095 205415332028289440422945643)
    ·
      refine ⟨308122998042434160634418465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205415332028289440422945643 308122998042434160634418465)
      ·
        refine ⟨231092248531825620475813849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308122998042434160634418465 231092248531825620475813849)
        ·
          refine ⟨173319186398869215356860387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231092248531825620475813849 173319186398869215356860387)
          ·
            refine ⟨259978779598303823035290581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173319186398869215356860387 259978779598303823035290581)
            ·
              refine ⟨6093252646835245852389623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 259978779598303823035290581 6093252646835245852389623)
              ·
                refine ⟨9139878970252868778584435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093252646835245852389623 9139878970252868778584435)
                ·
                  refine ⟨13709818455379303167876653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9139878970252868778584435 13709818455379303167876653)
                  ·
                    refine ⟨5141181920767238687953745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13709818455379303167876653 5141181920767238687953745)
                    ·
                      refine ⟨3855886440575429015965309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5141181920767238687953745 3855886440575429015965309)
                      ·
                        rfl

theorem cell23_7509312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_7509312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509312 prefixEnd_7509312 := by exact prefixLift 7509312
  have htrace : WordTrace (prefixWord ++ tailWord_7509312) baseStart_7509312 baseEnd_7509312 := by
    simpa [prefixWord, tailWord_7509312, baseEnd_7509312] using wordTrace_append hprefix tailTrace_7509312
  have hstable : (prefixWord ++ tailWord_7509312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509312).length < 2 ^ (prefixWord ++ tailWord_7509312).sum := by decide
  have hdescent : baseEnd_7509312 < baseStart_7509312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509331 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 7]
def baseStart_7509331 : Nat := 118140960795 + 7509331 * 2 ^ 59
def prefixEnd_7509331 : Nat := 4983230072969 + 3 ^ 40 * 7509331 * 2
def baseEnd_7509331 : Nat := 428432910745318271291969

theorem tailTrace_7509331 : CollatzResearch.WordTrace tailWord_7509331 prefixEnd_7509331 428432910745318271291969 := by
  unfold tailWord_7509331
  simp only [CollatzResearch.WordTrace]
  refine ⟨273887802357983753475535847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182591868238655835650357231 273887802357983753475535847)
  ·
    refine ⟨410831703536975630213303771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273887802357983753475535847 410831703536975630213303771)
    ·
      refine ⟨616247555305463445319955657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410831703536975630213303771 616247555305463445319955657)
      ·
        refine ⟨462185666479097583989966743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616247555305463445319955657 462185666479097583989966743)
        ·
          refine ⟨693278499718646375984950115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462185666479097583989966743 693278499718646375984950115)
          ·
            refine ⟨1039917749577969563977425173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693278499718646375984950115 1039917749577969563977425173)
            ·
              refine ⟨48746144511467323311441805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1039917749577969563977425173 48746144511467323311441805)
              ·
                refine ⟨18279804191800246241790677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48746144511467323311441805 18279804191800246241790677)
                ·
                  refine ⟨428432910745318271291969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18279804191800246241790677 428432910745318271291969)
                  ·
                    rfl

theorem cell23_7509331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 7].length) (baseStart_7509331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509331 prefixEnd_7509331 := by exact prefixLift 7509331
  have htrace : WordTrace (prefixWord ++ tailWord_7509331) baseStart_7509331 baseEnd_7509331 := by
    simpa [prefixWord, tailWord_7509331, baseEnd_7509331] using wordTrace_append hprefix tailTrace_7509331
  have hstable : (prefixWord ++ tailWord_7509331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509331).length < 2 ^ (prefixWord ++ tailWord_7509331).sum := by decide
  have hdescent : baseEnd_7509331 < baseStart_7509331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509348 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 7]
def baseStart_7509348 : Nat := 118140960795 + 7509348 * 2 ^ 59
def prefixEnd_7509348 : Nat := 4983230072969 + 3 ^ 40 * 7509348 * 2
def baseEnd_7509348 : Nat := 428433880653221208346127

theorem tailTrace_7509348 : CollatzResearch.WordTrace tailWord_7509348 prefixEnd_7509348 428433880653221208346127 := by
  unfold tailWord_7509348
  simp only [CollatzResearch.WordTrace]
  refine ⟨136944211199461082689452349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182592281599281443585936465 136944211199461082689452349)
  ·
    refine ⟨51354079199797906008544631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136944211199461082689452349 51354079199797906008544631)
    ·
      refine ⟨77031118799696859012816947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51354079199797906008544631 77031118799696859012816947)
      ·
        refine ⟨115546678199545288519225421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77031118799696859012816947 115546678199545288519225421)
        ·
          refine ⟨43330004324829483194709533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115546678199545288519225421 43330004324829483194709533)
          ·
            refine ⟨16248751621811056198016075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43330004324829483194709533 16248751621811056198016075)
            ·
              refine ⟨24373127432716584297024113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16248751621811056198016075 24373127432716584297024113)
              ·
                refine ⟨18279845574537438222768085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24373127432716584297024113 18279845574537438222768085)
                ·
                  refine ⟨428433880653221208346127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18279845574537438222768085 428433880653221208346127)
                  ·
                    rfl

theorem cell23_7509348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_7509348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509348 prefixEnd_7509348 := by exact prefixLift 7509348
  have htrace : WordTrace (prefixWord ++ tailWord_7509348) baseStart_7509348 baseEnd_7509348 := by
    simpa [prefixWord, tailWord_7509348, baseEnd_7509348] using wordTrace_append hprefix tailTrace_7509348
  have hstable : (prefixWord ++ tailWord_7509348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509348).length < 2 ^ (prefixWord ++ tailWord_7509348).sum := by decide
  have hdescent : baseEnd_7509348 < baseStart_7509348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509415 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7509415 : Nat := 118140960795 + 7509415 * 2 ^ 59
def prefixEnd_7509415 : Nat := 4983230072969 + 3 ^ 40 * 7509415 * 2
def baseEnd_7509415 : Nat := 3855939329082842112977335

theorem tailTrace_7509415 : CollatzResearch.WordTrace tailWord_7509415 prefixEnd_7509415 3855939329082842112977335 := by
  unfold tailWord_7509415
  simp only [CollatzResearch.WordTrace]
  refine ⟨273890866089679435821593699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182593910726452957214395799 273890866089679435821593699)
  ·
    refine ⟨410836299134519153732390549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273890866089679435821593699 410836299134519153732390549)
    ·
      refine ⟨19257951521930585331205807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 410836299134519153732390549 19257951521930585331205807)
      ·
        refine ⟨28886927282895877996808711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19257951521930585331205807 28886927282895877996808711)
        ·
          refine ⟨43330390924343816995213067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28886927282895877996808711 43330390924343816995213067)
          ·
            refine ⟨64995586386515725492819601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43330390924343816995213067 64995586386515725492819601)
            ·
              refine ⟨48746689789886794119614701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64995586386515725492819601 48746689789886794119614701)
              ·
                refine ⟨18280008671207547794855513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48746689789886794119614701 18280008671207547794855513)
                ·
                  refine ⟨13710006503405660846141635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18280008671207547794855513 13710006503405660846141635)
                  ·
                    refine ⟨20565009755108491269212453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13710006503405660846141635 20565009755108491269212453)
                    ·
                      refine ⟨3855939329082842112977335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20565009755108491269212453 3855939329082842112977335)
                      ·
                        rfl

theorem cell23_7509415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7509415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509415 prefixEnd_7509415 := by exact prefixLift 7509415
  have htrace : WordTrace (prefixWord ++ tailWord_7509415) baseStart_7509415 baseEnd_7509415 := by
    simpa [prefixWord, tailWord_7509415, baseEnd_7509415] using wordTrace_append hprefix tailTrace_7509415
  have hstable : (prefixWord ++ tailWord_7509415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509415).length < 2 ^ (prefixWord ++ tailWord_7509415).sum := by decide
  have hdescent : baseEnd_7509415 < baseStart_7509415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509416 : List Nat := [2, 1, 6, 1, 3, 1, 1, 3, 5]
def baseStart_7509416 : Nat := 118140960795 + 7509416 * 2 ^ 59
def prefixEnd_7509416 : Nat := 4983230072969 + 3 ^ 40 * 7509416 * 2
def baseEnd_7509416 : Nat := 428437760284832956562759

theorem tailTrace_7509416 : CollatzResearch.WordTrace tailWord_7509416 prefixEnd_7509416 428437760284832956562759 := by
  unfold tailWord_7509416
  simp only [CollatzResearch.WordTrace]
  refine ⟨136945451281337906496190051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182593935041783875328253401 136945451281337906496190051)
  ·
    refine ⟨205418176922006859744285077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136945451281337906496190051 205418176922006859744285077)
    ·
      refine ⟨9628977043219071550513363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205418176922006859744285077 9628977043219071550513363)
      ·
        refine ⟨14443465564828607325770045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9628977043219071550513363 14443465564828607325770045)
        ·
          refine ⟨5416299586810727747163767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14443465564828607325770045 5416299586810727747163767)
          ·
            refine ⟨8124449380216091620745651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416299586810727747163767 8124449380216091620745651)
            ·
              refine ⟨12186674070324137431118477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124449380216091620745651 12186674070324137431118477)
              ·
                refine ⟨4570002776371551536669429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12186674070324137431118477 4570002776371551536669429)
                ·
                  refine ⟨428437760284832956562759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4570002776371551536669429 428437760284832956562759)
                  ·
                    rfl

theorem cell23_7509416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 5].length) (baseStart_7509416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509416 prefixEnd_7509416 := by exact prefixLift 7509416
  have htrace : WordTrace (prefixWord ++ tailWord_7509416) baseStart_7509416 baseEnd_7509416 := by
    simpa [prefixWord, tailWord_7509416, baseEnd_7509416] using wordTrace_append hprefix tailTrace_7509416
  have hstable : (prefixWord ++ tailWord_7509416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509416).length < 2 ^ (prefixWord ++ tailWord_7509416).sum := by decide
  have hdescent : baseEnd_7509416 < baseStart_7509416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509455 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 6]
def baseStart_7509455 : Nat := 118140960795 + 7509455 * 2 ^ 59
def prefixEnd_7509455 : Nat := 4983230072969 + 3 ^ 40 * 7509455 * 2
def baseEnd_7509455 : Nat := 428439985367669106275239

theorem tailTrace_7509455 : CollatzResearch.WordTrace tailWord_7509455 prefixEnd_7509455 428439985367669106275239 := by
  unfold tailWord_7509455
  simp only [CollatzResearch.WordTrace]
  refine ⟨273892325009534522653049819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182594883339689681768699879 273892325009534522653049819)
  ·
    refine ⟨410838487514301783979574729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273892325009534522653049819 410838487514301783979574729)
    ·
      refine ⟨308128865635726337984681047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410838487514301783979574729 308128865635726337984681047)
      ·
        refine ⟨462193298453589506977021571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308128865635726337984681047 462193298453589506977021571)
        ·
          refine ⟨693289947680384260465532357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462193298453589506977021571 693289947680384260465532357)
          ·
            refine ⟨129991865190072048837287317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 693289947680384260465532357 129991865190072048837287317)
            ·
              refine ⟨6093368680784627289247843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129991865190072048837287317 6093368680784627289247843)
              ·
                refine ⟨9140053021176940933871765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093368680784627289247843 9140053021176940933871765)
                ·
                  refine ⟨428439985367669106275239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9140053021176940933871765 428439985367669106275239)
                  ·
                    rfl

theorem cell23_7509455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 6].length) (baseStart_7509455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509455 prefixEnd_7509455 := by exact prefixLift 7509455
  have htrace : WordTrace (prefixWord ++ tailWord_7509455) baseStart_7509455 baseEnd_7509455 := by
    simpa [prefixWord, tailWord_7509455, baseEnd_7509455] using wordTrace_append hprefix tailTrace_7509455
  have hstable : (prefixWord ++ tailWord_7509455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509455).length < 2 ^ (prefixWord ++ tailWord_7509455).sum := by decide
  have hdescent : baseEnd_7509455 < baseStart_7509455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509493 : List Nat := [1, 3, 5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7509493 : Nat := 118140960795 + 7509493 * 2 ^ 59
def prefixEnd_7509493 : Nat := 4983230072969 + 3 ^ 40 * 7509493 * 2
def baseEnd_7509493 : Nat := 1285326460191297602600659

theorem tailTrace_7509493 : CollatzResearch.WordTrace tailWord_7509493 prefixEnd_7509493 1285326460191297602600659 := by
  unfold tailWord_7509493
  simp only [CollatzResearch.WordTrace]
  refine ⟨273893710983396855142933133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182595807322264570095288755 273893710983396855142933133)
  ·
    refine ⟨102710141618773820678599925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273893710983396855142933133 102710141618773820678599925)
    ·
      refine ⟨9629075776760045688618743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102710141618773820678599925 9629075776760045688618743)
      ·
        refine ⟨14443613665140068532928115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9629075776760045688618743 14443613665140068532928115)
        ·
          refine ⟨21665420497710102799392173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14443613665140068532928115 21665420497710102799392173)
          ·
            refine ⟨8124532686641288549772065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21665420497710102799392173 8124532686641288549772065)
            ·
              refine ⟨6093399514980966412329049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8124532686641288549772065 6093399514980966412329049)
              ·
                refine ⟨4570049636235724809246787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6093399514980966412329049 4570049636235724809246787)
                ·
                  refine ⟨6855074454353587213870181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570049636235724809246787 6855074454353587213870181)
                  ·
                    refine ⟨1285326460191297602600659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6855074454353587213870181 1285326460191297602600659)
                    ·
                      rfl

theorem cell23_7509493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7509493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509493 prefixEnd_7509493 := by exact prefixLift 7509493
  have htrace : WordTrace (prefixWord ++ tailWord_7509493) baseStart_7509493 baseEnd_7509493 := by
    simpa [prefixWord, tailWord_7509493, baseEnd_7509493] using wordTrace_append hprefix tailTrace_7509493
  have hstable : (prefixWord ++ tailWord_7509493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509493).length < 2 ^ (prefixWord ++ tailWord_7509493).sum := by decide
  have hdescent : baseEnd_7509493 < baseStart_7509493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509498 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_7509498 : Nat := 118140960795 + 7509498 * 2 ^ 59
def prefixEnd_7509498 : Nat := 4983230072969 + 3 ^ 40 * 7509498 * 2
def baseEnd_7509498 : Nat := 1285327315992388429413151

theorem tailTrace_7509498 : CollatzResearch.WordTrace tailWord_7509498 prefixEnd_7509498 1285327315992388429413151 := by
  unfold tailWord_7509498
  simp only [CollatzResearch.WordTrace]
  refine ⟨68473473337094685249216287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182595928898919160664576765 68473473337094685249216287)
  ·
    refine ⟨102710210005642027873824431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68473473337094685249216287 102710210005642027873824431)
    ·
      refine ⟨154065315008463041810736647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102710210005642027873824431 154065315008463041810736647)
      ·
        refine ⟨231097972512694562716104971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154065315008463041810736647 231097972512694562716104971)
        ·
          refine ⟨346646958769041844074157457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231097972512694562716104971 346646958769041844074157457)
          ·
            refine ⟨259985219076781383055618093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346646958769041844074157457 259985219076781383055618093)
            ·
              refine ⟨97494457153793018645856785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259985219076781383055618093 97494457153793018645856785)
              ·
                refine ⟨73120842865344763984392589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97494457153793018645856785 73120842865344763984392589)
                ·
                  refine ⟨27420316074504286494147221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73120842865344763984392589 27420316074504286494147221)
                  ·
                    refine ⟨1285327315992388429413151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27420316074504286494147221 1285327315992388429413151)
                    ·
                      rfl

theorem cell23_7509498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_7509498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509498 prefixEnd_7509498 := by exact prefixLift 7509498
  have htrace : WordTrace (prefixWord ++ tailWord_7509498) baseStart_7509498 baseEnd_7509498 := by
    simpa [prefixWord, tailWord_7509498, baseEnd_7509498] using wordTrace_append hprefix tailTrace_7509498
  have hstable : (prefixWord ++ tailWord_7509498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509498).length < 2 ^ (prefixWord ++ tailWord_7509498).sum := by decide
  have hdescent : baseEnd_7509498 < baseStart_7509498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509535 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_7509535 : Nat := 118140960795 + 7509535 * 2 ^ 59
def prefixEnd_7509535 : Nat := 4983230072969 + 3 ^ 40 * 7509535 * 2
def baseEnd_7509535 : Nat := 3856000946761381643476783

theorem tailTrace_7509535 : CollatzResearch.WordTrace tailWord_7509535 prefixEnd_7509535 3856000946761381643476783 := by
  unfold tailWord_7509535
  simp only [CollatzResearch.WordTrace]
  refine ⟨273895242849244696315962059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182596828566163130877308039 273895242849244696315962059)
  ·
    refine ⟨410842864273867044473943089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273895242849244696315962059 410842864273867044473943089)
    ·
      refine ⟨308132148205400283355457317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410842864273867044473943089 308132148205400283355457317)
      ·
        refine ⟨57774777788512553129148247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308132148205400283355457317 57774777788512553129148247)
        ·
          refine ⟨86662166682768829693722371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57774777788512553129148247 86662166682768829693722371)
          ·
            refine ⟨129993250024153244540583557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86662166682768829693722371 129993250024153244540583557)
            ·
              refine ⟨24373734379528733351359417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129993250024153244540583557 24373734379528733351359417)
              ·
                refine ⟨18280300784646550013519563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24373734379528733351359417 18280300784646550013519563)
                ·
                  refine ⟨27420451176969825020279345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18280300784646550013519563 27420451176969825020279345)
                  ·
                    refine ⟨20565338382727368765209509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27420451176969825020279345 20565338382727368765209509)
                    ·
                      refine ⟨3856000946761381643476783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20565338382727368765209509 3856000946761381643476783)
                      ·
                        rfl

theorem cell23_7509535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_7509535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509535 prefixEnd_7509535 := by exact prefixLift 7509535
  have htrace : WordTrace (prefixWord ++ tailWord_7509535) baseStart_7509535 baseEnd_7509535 := by
    simpa [prefixWord, tailWord_7509535, baseEnd_7509535] using wordTrace_append hprefix tailTrace_7509535
  have hstable : (prefixWord ++ tailWord_7509535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509535).length < 2 ^ (prefixWord ++ tailWord_7509535).sum := by decide
  have hdescent : baseEnd_7509535 < baseStart_7509535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509548 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_7509548 : Nat := 118140960795 + 7509548 * 2 ^ 59
def prefixEnd_7509548 : Nat := 4983230072969 + 3 ^ 40 * 7509548 * 2
def baseEnd_7509548 : Nat := 3856007622009890092614223

theorem tailTrace_7509548 : CollatzResearch.WordTrace tailWord_7509548 prefixEnd_7509548 3856007622009890092614223 := by
  unfold tailWord_7509548
  simp only [CollatzResearch.WordTrace]
  refine ⟨136947858499098799768092649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182597144665465066357456865 136947858499098799768092649)
  ·
    refine ⟨102710893874324099826069487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136947858499098799768092649 102710893874324099826069487)
    ·
      refine ⟨154066340811486149739104231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102710893874324099826069487 154066340811486149739104231)
      ·
        refine ⟨231099511217229224608656347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154066340811486149739104231 231099511217229224608656347)
        ·
          refine ⟨346649266825843836912984521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231099511217229224608656347 346649266825843836912984521)
          ·
            refine ⟨259986950119382877684738391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346649266825843836912984521 259986950119382877684738391)
            ·
              refine ⟨389980425179074316527107587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259986950119382877684738391 389980425179074316527107587)
              ·
                refine ⟨584970637768611474790661381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389980425179074316527107587 584970637768611474790661381)
                ·
                  refine ⟨109681994581614651523249009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 584970637768611474790661381 109681994581614651523249009)
                  ·
                    refine ⟨82261495936210988642436757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109681994581614651523249009 82261495936210988642436757)
                    ·
                      refine ⟨3856007622009890092614223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82261495936210988642436757 3856007622009890092614223)
                      ·
                        rfl

theorem cell23_7509548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_7509548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509548 prefixEnd_7509548 := by exact prefixLift 7509548
  have htrace : WordTrace (prefixWord ++ tailWord_7509548) baseStart_7509548 baseEnd_7509548 := by
    simpa [prefixWord, tailWord_7509548, baseEnd_7509548] using wordTrace_append hprefix tailTrace_7509548
  have hstable : (prefixWord ++ tailWord_7509548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509548).length < 2 ^ (prefixWord ++ tailWord_7509548).sum := by decide
  have hdescent : baseEnd_7509548 < baseStart_7509548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509615 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 3]
def baseStart_7509615 : Nat := 118140960795 + 7509615 * 2 ^ 59
def prefixEnd_7509615 : Nat := 4983230072969 + 3 ^ 40 * 7509615 * 2
def baseEnd_7509615 : Nat := 3856042025213741330476415

theorem tailTrace_7509615 : CollatzResearch.WordTrace tailWord_7509615 prefixEnd_7509615 3856042025213741330476415 := by
  unfold tailWord_7509615
  simp only [CollatzResearch.WordTrace]
  refine ⟨273898160688954869978874299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182598773792636579985916199 273898160688954869978874299)
  ·
    refine ⟨410847241033432304968311449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273898160688954869978874299 410847241033432304968311449)
    ·
      refine ⟨308135430775074228726233587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410847241033432304968311449 308135430775074228726233587)
      ·
        refine ⟨462203146162611343089350381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308135430775074228726233587 462203146162611343089350381)
        ·
          refine ⟨173326179810979253658506393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462203146162611343089350381 173326179810979253658506393)
          ·
            refine ⟨129994634858234440243879795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173326179810979253658506393 129994634858234440243879795)
            ·
              refine ⟨194991952287351660365819693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129994634858234440243879795 194991952287351660365819693)
              ·
                refine ⟨73121982107756872637182385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194991952287351660365819693 73121982107756872637182385)
                ·
                  refine ⟨54841486580817654477886789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73121982107756872637182385 54841486580817654477886789)
                  ·
                    refine ⟨10282778733903310214603773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54841486580817654477886789 10282778733903310214603773)
                    ·
                      refine ⟨3856042025213741330476415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10282778733903310214603773 3856042025213741330476415)
                      ·
                        rfl

theorem cell23_7509615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_7509615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509615 prefixEnd_7509615 := by exact prefixLift 7509615
  have htrace : WordTrace (prefixWord ++ tailWord_7509615) baseStart_7509615 baseEnd_7509615 := by
    simpa [prefixWord, tailWord_7509615, baseEnd_7509615] using wordTrace_append hprefix tailTrace_7509615
  have hstable : (prefixWord ++ tailWord_7509615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509615).length < 2 ^ (prefixWord ++ tailWord_7509615).sum := by decide
  have hdescent : baseEnd_7509615 < baseStart_7509615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509625 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_7509625 : Nat := 118140960795 + 7509625 * 2 ^ 59
def prefixEnd_7509625 : Nat := 4983230072969 + 3 ^ 40 * 7509625 * 2
def baseEnd_7509625 : Nat := 3856047160020286291351369

theorem tailTrace_7509625 : CollatzResearch.WordTrace tailWord_7509625 prefixEnd_7509625 3856047160020286291351369 := by
  unfold tailWord_7509625
  simp only [CollatzResearch.WordTrace]
  refine ⟨273898525418918641686738329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182599016945945761124492219 273898525418918641686738329)
  ·
    refine ⟨205423894064188981265053747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273898525418918641686738329 205423894064188981265053747)
    ·
      refine ⟨308135841096283471897580621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205423894064188981265053747 308135841096283471897580621)
      ·
        refine ⟨115550940411106301961592733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308135841096283471897580621 115550940411106301961592733)
        ·
          refine ⟨43331602654164863235597275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115550940411106301961592733 43331602654164863235597275)
          ·
            refine ⟨64997403981247294853395913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43331602654164863235597275 64997403981247294853395913)
            ·
              refine ⟨48748052985935471140046935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64997403981247294853395913 48748052985935471140046935)
              ·
                refine ⟨73122079478903206710070403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48748052985935471140046935 73122079478903206710070403)
                ·
                  refine ⟨109683119218354810065105605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73122079478903206710070403 109683119218354810065105605)
                  ·
                    refine ⟨20565584853441526887207301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109683119218354810065105605 20565584853441526887207301)
                    ·
                      refine ⟨3856047160020286291351369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20565584853441526887207301 3856047160020286291351369)
                      ·
                        rfl

theorem cell23_7509625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_7509625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509625 prefixEnd_7509625 := by exact prefixLift 7509625
  have htrace : WordTrace (prefixWord ++ tailWord_7509625) baseStart_7509625 baseEnd_7509625 := by
    simpa [prefixWord, tailWord_7509625, baseEnd_7509625] using wordTrace_append hprefix tailTrace_7509625
  have hstable : (prefixWord ++ tailWord_7509625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509625).length < 2 ^ (prefixWord ++ tailWord_7509625).sum := by decide
  have hdescent : baseEnd_7509625 < baseStart_7509625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509669 : List Nat := [1, 3, 1, 2, 1, 2, 6, 2, 5]
def baseStart_7509669 : Nat := 118140960795 + 7509669 * 2 ^ 59
def prefixEnd_7509669 : Nat := 4983230072969 + 3 ^ 40 * 7509669 * 2
def baseEnd_7509669 : Nat := 428452194796564902133463

theorem tailTrace_7509669 : CollatzResearch.WordTrace tailWord_7509669 prefixEnd_7509669 428452194796564902133463 := by
  unfold tailWord_7509669
  simp only [CollatzResearch.WordTrace]
  refine ⟨273900130230759237201340061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182600086820506158134226707 273900130230759237201340061)
  ·
    refine ⟨102712548836534713950502523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273900130230759237201340061 102712548836534713950502523)
    ·
      refine ⟨154068823254802070925753785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102712548836534713950502523 154068823254802070925753785)
      ·
        refine ⟨115551617441101553194315339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154068823254802070925753785 115551617441101553194315339)
        ·
          refine ⟨173327426161652329791473009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115551617441101553194315339 173327426161652329791473009)
          ·
            refine ⟨129995569621239247343604757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173327426161652329791473009 129995569621239247343604757)
            ·
              refine ⟨6093542325995589719231473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129995569621239247343604757 6093542325995589719231473)
              ·
                refine ⟨4570156744496692289423605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6093542325995589719231473 4570156744496692289423605)
                ·
                  refine ⟨428452194796564902133463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4570156744496692289423605 428452194796564902133463)
                  ·
                    rfl

theorem cell23_7509669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_7509669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509669 prefixEnd_7509669 := by exact prefixLift 7509669
  have htrace : WordTrace (prefixWord ++ tailWord_7509669) baseStart_7509669 baseEnd_7509669 := by
    simpa [prefixWord, tailWord_7509669, baseEnd_7509669] using wordTrace_append hprefix tailTrace_7509669
  have hstable : (prefixWord ++ tailWord_7509669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509669).length < 2 ^ (prefixWord ++ tailWord_7509669).sum := by decide
  have hdescent : baseEnd_7509669 < baseStart_7509669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509786 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3]
def baseStart_7509786 : Nat := 118140960795 + 7509786 * 2 ^ 59
def prefixEnd_7509786 : Nat := 4983230072969 + 3 ^ 40 * 7509786 * 2
def baseEnd_7509786 : Nat := 3856129830405660161438129

theorem tailTrace_7509786 : CollatzResearch.WordTrace tailWord_7509786 prefixEnd_7509786 3856129830405660161438129 := by
  unfold tailWord_7509786
  simp only [CollatzResearch.WordTrace]
  refine ⟨68476099392833841545837303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182602931714223577455566141 68476099392833841545837303)
  ·
    refine ⟨102714149089250762318755955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68476099392833841545837303 102714149089250762318755955)
    ·
      refine ⟨154071223633876143478133933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102714149089250762318755955 154071223633876143478133933)
      ·
        refine ⟨57776708862703553804300225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154071223633876143478133933 57776708862703553804300225)
        ·
          refine ⟨43332531647027665353225169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57776708862703553804300225 43332531647027665353225169)
          ·
            refine ⟨32499398735270749014918877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43332531647027665353225169 32499398735270749014918877)
            ·
              refine ⟨12187274525726530880594579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32499398735270749014918877 12187274525726530880594579)
              ·
                refine ⟨18280911788589796320891869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12187274525726530880594579 18280911788589796320891869)
                ·
                  refine ⟨6855341920721173620334451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18280911788589796320891869 6855341920721173620334451)
                  ·
                    refine ⟨10283012881081760430501677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6855341920721173620334451 10283012881081760430501677)
                    ·
                      refine ⟨3856129830405660161438129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10283012881081760430501677 3856129830405660161438129)
                      ·
                        rfl

theorem cell23_7509786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_7509786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509786 prefixEnd_7509786 := by exact prefixLift 7509786
  have htrace : WordTrace (prefixWord ++ tailWord_7509786) baseStart_7509786 baseEnd_7509786 := by
    simpa [prefixWord, tailWord_7509786, baseEnd_7509786] using wordTrace_append hprefix tailTrace_7509786
  have hstable : (prefixWord ++ tailWord_7509786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509786).length < 2 ^ (prefixWord ++ tailWord_7509786).sum := by decide
  have hdescent : baseEnd_7509786 < baseStart_7509786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509806 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_7509806 : Nat := 118140960795 + 7509806 * 2 ^ 59
def prefixEnd_7509806 : Nat := 4983230072969 + 3 ^ 40 * 7509806 * 2
def baseEnd_7509806 : Nat := 1285380033339583361062679

theorem tailTrace_7509806 : CollatzResearch.WordTrace tailWord_7509806 prefixEnd_7509806 1285380033339583361062679 := by
  unfold tailWord_7509806
  simp only [CollatzResearch.WordTrace]
  refine ⟨34238140878907863699884659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182603418020841939732718181 34238140878907863699884659)
  ·
    refine ⟨51357211318361795549826989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34238140878907863699884659 51357211318361795549826989)
    ·
      refine ⟨19258954244385673331185121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51357211318361795549826989 19258954244385673331185121)
      ·
        refine ⟨14444215683289254998388841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19258954244385673331185121 14444215683289254998388841)
        ·
          refine ⟨10833161762466941248791631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14444215683289254998388841 10833161762466941248791631)
          ·
            refine ⟨16249742643700411873187447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833161762466941248791631 16249742643700411873187447)
            ·
              refine ⟨24374613965550617809781171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16249742643700411873187447 24374613965550617809781171)
              ·
                refine ⟨36561920948325926714671757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24374613965550617809781171 36561920948325926714671757)
                ·
                  refine ⟨13710720355622222518001909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36561920948325926714671757 13710720355622222518001909)
                  ·
                    refine ⟨1285380033339583361062679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13710720355622222518001909 1285380033339583361062679)
                    ·
                      rfl

theorem cell23_7509806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_7509806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509806 prefixEnd_7509806 := by exact prefixLift 7509806
  have htrace : WordTrace (prefixWord ++ tailWord_7509806) baseStart_7509806 baseEnd_7509806 := by
    simpa [prefixWord, tailWord_7509806, baseEnd_7509806] using wordTrace_append hprefix tailTrace_7509806
  have hstable : (prefixWord ++ tailWord_7509806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509806).length < 2 ^ (prefixWord ++ tailWord_7509806).sum := by decide
  have hdescent : baseEnd_7509806 < baseStart_7509806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509809 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_7509809 : Nat := 118140960795 + 7509809 * 2 ^ 59
def prefixEnd_7509809 : Nat := 4983230072969 + 3 ^ 40 * 7509809 * 2
def baseEnd_7509809 : Nat := 3856141640460713571450523

theorem tailTrace_7509809 : CollatzResearch.WordTrace tailWord_7509809 prefixEnd_7509809 3856141640460713571450523 := by
  unfold tailWord_7509809
  simp only [CollatzResearch.WordTrace]
  refine ⟨273905236450252041111436481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182603490966834694074290987 273905236450252041111436481)
  ·
    refine ⟨205428927337689030833577361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273905236450252041111436481 205428927337689030833577361)
    ·
      refine ⟨154071695503266773125183021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205428927337689030833577361 154071695503266773125183021)
      ·
        refine ⟨57776885813725039921943633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154071695503266773125183021 57776885813725039921943633)
        ·
          refine ⟨43332664360293779941457725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57776885813725039921943633 43332664360293779941457725)
          ·
            refine ⟨16249749135110167478046647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43332664360293779941457725 16249749135110167478046647)
            ·
              refine ⟨24374623702665251217069971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16249749135110167478046647 24374623702665251217069971)
              ·
                refine ⟨36561935553997876825604957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24374623702665251217069971 36561935553997876825604957)
                ·
                  refine ⟨13710725832749203809601859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36561935553997876825604957 13710725832749203809601859)
                  ·
                    refine ⟨20566088749123805714402789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13710725832749203809601859 20566088749123805714402789)
                    ·
                      refine ⟨3856141640460713571450523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20566088749123805714402789 3856141640460713571450523)
                      ·
                        rfl

theorem cell23_7509809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_7509809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509809 prefixEnd_7509809 := by exact prefixLift 7509809
  have htrace : WordTrace (prefixWord ++ tailWord_7509809) baseStart_7509809 baseEnd_7509809 := by
    simpa [prefixWord, tailWord_7509809, baseEnd_7509809] using wordTrace_append hprefix tailTrace_7509809
  have hstable : (prefixWord ++ tailWord_7509809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509809).length < 2 ^ (prefixWord ++ tailWord_7509809).sum := by decide
  have hdescent : baseEnd_7509809 < baseStart_7509809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509813 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_7509813 : Nat := 118140960795 + 7509813 * 2 ^ 59
def prefixEnd_7509813 : Nat := 4983230072969 + 3 ^ 40 * 7509813 * 2
def baseEnd_7509813 : Nat := 3856143694383331555800505

theorem tailTrace_7509813 : CollatzResearch.WordTrace tailWord_7509813 prefixEnd_7509813 3856143694383331555800505 := by
  unfold tailWord_7509813
  simp only [CollatzResearch.WordTrace]
  refine ⟨273905382342237549794582093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182603588228158366529721395 273905382342237549794582093)
  ·
    refine ⟨102714518378339081172968285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273905382342237549794582093 102714518378339081172968285)
    ·
      refine ⟨38517944391877155439863107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102714518378339081172968285 38517944391877155439863107)
      ·
        refine ⟨57776916587815733159794661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38517944391877155439863107 57776916587815733159794661)
        ·
          refine ⟨10833171860215449967461499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57776916587815733159794661 10833171860215449967461499)
          ·
            refine ⟨16249757790323174951192249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833171860215449967461499 16249757790323174951192249)
            ·
              refine ⟨12187318342742381213394187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16249757790323174951192249 12187318342742381213394187)
              ·
                refine ⟨18280977514113571820091281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12187318342742381213394187 18280977514113571820091281)
                ·
                  refine ⟨13710733135585178865068461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18280977514113571820091281 13710733135585178865068461)
                  ·
                    refine ⟨5141524925844442074400673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13710733135585178865068461 5141524925844442074400673)
                    ·
                      refine ⟨3856143694383331555800505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5141524925844442074400673 3856143694383331555800505)
                      ·
                        rfl

theorem cell23_7509813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_7509813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509813 prefixEnd_7509813 := by exact prefixLift 7509813
  have htrace : WordTrace (prefixWord ++ tailWord_7509813) baseStart_7509813 baseEnd_7509813 := by
    simpa [prefixWord, tailWord_7509813, baseEnd_7509813] using wordTrace_append hprefix tailTrace_7509813
  have hstable : (prefixWord ++ tailWord_7509813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509813).length < 2 ^ (prefixWord ++ tailWord_7509813).sum := by decide
  have hdescent : baseEnd_7509813 < baseStart_7509813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509830 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7509830 : Nat := 118140960795 + 7509830 * 2 ^ 59
def prefixEnd_7509830 : Nat := 4983230072969 + 3 ^ 40 * 7509830 * 2
def baseEnd_7509830 : Nat := 3856152423554457989287927

theorem tailTrace_7509830 : CollatzResearch.WordTrace tailWord_7509830 prefixEnd_7509830 3856152423554457989287927 := by
  unfold tailWord_7509830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8559562574474248803060967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182604001588783974465300629 8559562574474248803060967)
  ·
    refine ⟨12839343861711373204591451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8559562574474248803060967 12839343861711373204591451)
    ·
      refine ⟨19259015792567059806887177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12839343861711373204591451 19259015792567059806887177)
      ·
        refine ⟨14444261844425294855165383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19259015792567059806887177 14444261844425294855165383)
        ·
          refine ⟨21666392766637942282748075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14444261844425294855165383 21666392766637942282748075)
          ·
            refine ⟨32499589149956913424122113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21666392766637942282748075 32499589149956913424122113)
            ·
              refine ⟨24374691862467685068091585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32499589149956913424122113 24374691862467685068091585)
              ·
                refine ⟨18281018896850763801068689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24374691862467685068091585 18281018896850763801068689)
                ·
                  refine ⟨13710764172638072850801517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18281018896850763801068689 13710764172638072850801517)
                  ·
                    refine ⟨5141536564739277319050569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13710764172638072850801517 5141536564739277319050569)
                    ·
                      refine ⟨3856152423554457989287927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5141536564739277319050569 3856152423554457989287927)
                      ·
                        rfl

theorem cell23_7509830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7509830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509830 prefixEnd_7509830 := by exact prefixLift 7509830
  have htrace : WordTrace (prefixWord ++ tailWord_7509830) baseStart_7509830 baseEnd_7509830 := by
    simpa [prefixWord, tailWord_7509830, baseEnd_7509830] using wordTrace_append hprefix tailTrace_7509830
  have hstable : (prefixWord ++ tailWord_7509830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509830).length < 2 ^ (prefixWord ++ tailWord_7509830).sum := by decide
  have hdescent : baseEnd_7509830 < baseStart_7509830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509837 : List Nat := [1, 6, 1, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_7509837 : Nat := 118140960795 + 7509837 * 2 ^ 59
def prefixEnd_7509837 : Nat := 4983230072969 + 3 ^ 40 * 7509837 * 2
def baseEnd_7509837 : Nat := 3856156017919039461900395

theorem tailTrace_7509837 : CollatzResearch.WordTrace tailWord_7509837 prefixEnd_7509837 3856156017919039461900395 := by
  unfold tailWord_7509837
  simp only [CollatzResearch.WordTrace]
  refine ⟨273906257694150601893455765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182604171796100401262303843 273906257694150601893455765)
  ·
    refine ⟨12839355829413309463755739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 273906257694150601893455765 12839355829413309463755739)
    ·
      refine ⟨19259033744119964195633609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12839355829413309463755739 19259033744119964195633609)
      ·
        refine ⟨14444275308089973146725207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19259033744119964195633609 14444275308089973146725207)
        ·
          refine ⟨21666412962134959720087811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14444275308089973146725207 21666412962134959720087811)
          ·
            refine ⟨32499619443202439580131717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21666412962134959720087811 32499619443202439580131717)
            ·
              refine ⟨6093678645600457421274697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32499619443202439580131717 6093678645600457421274697)
              ·
                refine ⟨4570258984200343065956023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6093678645600457421274697 4570258984200343065956023)
                ·
                  refine ⟨6855388476300514598934035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570258984200343065956023 6855388476300514598934035)
                  ·
                    refine ⟨10283082714450771898401053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6855388476300514598934035 10283082714450771898401053)
                    ·
                      refine ⟨3856156017919039461900395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10283082714450771898401053 3856156017919039461900395)
                      ·
                        rfl

theorem cell23_7509837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_7509837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509837 prefixEnd_7509837 := by exact prefixLift 7509837
  have htrace : WordTrace (prefixWord ++ tailWord_7509837) baseStart_7509837 baseEnd_7509837 := by
    simpa [prefixWord, tailWord_7509837, baseEnd_7509837] using wordTrace_append hprefix tailTrace_7509837
  have hstable : (prefixWord ++ tailWord_7509837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509837).length < 2 ^ (prefixWord ++ tailWord_7509837).sum := by decide
  have hdescent : baseEnd_7509837 < baseStart_7509837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509872 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_7509872 : Nat := 118140960795 + 7509872 * 2 ^ 59
def prefixEnd_7509872 : Nat := 4983230072969 + 3 ^ 40 * 7509872 * 2
def baseEnd_7509872 : Nat := 3856173989741946824962733

theorem tailTrace_7509872 : CollatzResearch.WordTrace tailWord_7509872 prefixEnd_7509872 3856173989741946824962733 := by
  unfold tailWord_7509872
  simp only [CollatzResearch.WordTrace]
  refine ⟨136953767124511901435489935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182605022832682535247319913 136953767124511901435489935)
  ·
    refine ⟨205430650686767852153234903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136953767124511901435489935 205430650686767852153234903)
    ·
      refine ⟨308145976030151778229852355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205430650686767852153234903 308145976030151778229852355)
      ·
        refine ⟨462218964045227667344778533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308145976030151778229852355 462218964045227667344778533)
        ·
          refine ⟨86666055758480187627145975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 462218964045227667344778533 86666055758480187627145975)
          ·
            refine ⟨129999083637720281440718963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86666055758480187627145975 129999083637720281440718963)
            ·
              refine ⟨194998625456580422161078445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129999083637720281440718963 194998625456580422161078445)
              ·
                refine ⟨73124484546217658310404417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194998625456580422161078445 73124484546217658310404417)
                ·
                  refine ⟨54843363409663243732803313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73124484546217658310404417 54843363409663243732803313)
                  ·
                    refine ⟨41132522557247432799602485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54843363409663243732803313 41132522557247432799602485)
                    ·
                      refine ⟨3856173989741946824962733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41132522557247432799602485 3856173989741946824962733)
                      ·
                        rfl

theorem cell23_7509872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_7509872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509872 prefixEnd_7509872 := by exact prefixLift 7509872
  have htrace : WordTrace (prefixWord ++ tailWord_7509872) baseStart_7509872 baseEnd_7509872 := by
    simpa [prefixWord, tailWord_7509872, baseEnd_7509872] using wordTrace_append hprefix tailTrace_7509872
  have hstable : (prefixWord ++ tailWord_7509872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509872).length < 2 ^ (prefixWord ++ tailWord_7509872).sum := by decide
  have hdescent : baseEnd_7509872 < baseStart_7509872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7509932 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_7509932 : Nat := 118140960795 + 7509932 * 2 ^ 59
def prefixEnd_7509932 : Nat := 4983230072969 + 3 ^ 40 * 7509932 * 2
def baseEnd_7509932 : Nat := 3856204798581216590212457

theorem tailTrace_7509932 : CollatzResearch.WordTrace tailWord_7509932 prefixEnd_7509932 3856204798581216590212457 := by
  unfold tailWord_7509932
  simp only [CollatzResearch.WordTrace]
  refine ⟨136954861314403216559082025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182606481752537622078776033 136954861314403216559082025)
  ·
    refine ⟨102716145985802412419311519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136954861314403216559082025 102716145985802412419311519)
    ·
      refine ⟨154074218978703618628967279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102716145985802412419311519 154074218978703618628967279)
      ·
        refine ⟨231111328468055427943450919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154074218978703618628967279 231111328468055427943450919)
        ·
          refine ⟨346666992702083141915176379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231111328468055427943450919 346666992702083141915176379)
          ·
            refine ⟨520000489053124712872764569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346666992702083141915176379 520000489053124712872764569)
            ·
              refine ⟨390000366789843534654573427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520000489053124712872764569 390000366789843534654573427)
              ·
                refine ⟨585000550184765301981860141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390000366789843534654573427 585000550184765301981860141)
                ·
                  refine ⟨219375206319286988243197553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585000550184765301981860141 219375206319286988243197553)
                  ·
                    refine ⟨164531404739465241182398165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 219375206319286988243197553 164531404739465241182398165)
                    ·
                      refine ⟨3856204798581216590212457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164531404739465241182398165 3856204798581216590212457)
                      ·
                        rfl

theorem cell23_7509932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_7509932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7509932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7509932 prefixEnd_7509932 := by exact prefixLift 7509932
  have htrace : WordTrace (prefixWord ++ tailWord_7509932) baseStart_7509932 baseEnd_7509932 := by
    simpa [prefixWord, tailWord_7509932, baseEnd_7509932] using wordTrace_append hprefix tailTrace_7509932
  have hstable : (prefixWord ++ tailWord_7509932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7509932).length < 2 ^ (prefixWord ++ tailWord_7509932).sum := by decide
  have hdescent : baseEnd_7509932 < baseStart_7509932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7509932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510023 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_7510023 : Nat := 118140960795 + 7510023 * 2 ^ 59
def prefixEnd_7510023 : Nat := 4983230072969 + 3 ^ 40 * 7510023 * 2
def baseEnd_7510023 : Nat := 3856251525320775734174539

theorem tailTrace_7510023 : CollatzResearch.WordTrace tailWord_7510023 prefixEnd_7510023 3856251525320775734174539 := by
  unfold tailWord_7510023
  simp only [CollatzResearch.WordTrace]
  refine ⟨273913041671476755659726723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182608694447651170439817815 273913041671476755659726723)
  ·
    refine ⟨410869562507215133489590085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273913041671476755659726723 410869562507215133489590085)
    ·
      refine ⟨77038042970102837529298141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410869562507215133489590085 77038042970102837529298141)
      ·
        refine ⟨28889266113788564073486803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77038042970102837529298141 28889266113788564073486803)
        ·
          refine ⟨43333899170682846110230205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28889266113788564073486803 43333899170682846110230205)
          ·
            refine ⟨16250212189006067291336327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43333899170682846110230205 16250212189006067291336327)
            ·
              refine ⟨24375318283509100937004491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16250212189006067291336327 24375318283509100937004491)
              ·
                refine ⟨36562977425263651405506737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24375318283509100937004491 36562977425263651405506737)
                ·
                  refine ⟨27422233068947738554130053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36562977425263651405506737 27422233068947738554130053)
                  ·
                    refine ⟨5141668700427700978899385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27422233068947738554130053 5141668700427700978899385)
                    ·
                      refine ⟨3856251525320775734174539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5141668700427700978899385 3856251525320775734174539)
                      ·
                        rfl

theorem cell23_7510023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_7510023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510023 prefixEnd_7510023 := by exact prefixLift 7510023
  have htrace : WordTrace (prefixWord ++ tailWord_7510023) baseStart_7510023 baseEnd_7510023 := by
    simpa [prefixWord, tailWord_7510023, baseEnd_7510023] using wordTrace_append hprefix tailTrace_7510023
  have hstable : (prefixWord ++ tailWord_7510023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510023).length < 2 ^ (prefixWord ++ tailWord_7510023).sum := by decide
  have hdescent : baseEnd_7510023 < baseStart_7510023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510050 : List Nat := [3, 3, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_7510050 : Nat := 118140960795 + 7510050 * 2 ^ 59
def prefixEnd_7510050 : Nat := 4983230072969 + 3 ^ 40 * 7510050 * 2
def baseEnd_7510050 : Nat := 1285421796432815709512305

theorem tailTrace_7510050 : CollatzResearch.WordTrace tailWord_7510050 prefixEnd_7510050 1285421796432815709512305 := by
  unfold tailWord_7510050
  simp only [CollatzResearch.WordTrace]
  refine ⟨68478506610594734817739901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182609350961585959513973069 68478506610594734817739901)
  ·
    refine ⟨25679439978973025556652463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68478506610594734817739901 25679439978973025556652463)
    ·
      refine ⟨38519159968459538334978695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25679439978973025556652463 38519159968459538334978695)
      ·
        refine ⟨57778739952689307502468043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38519159968459538334978695 57778739952689307502468043)
        ·
          refine ⟨86668109929033961253702065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57778739952689307502468043 86668109929033961253702065)
          ·
            refine ⟨65001082446775470940276549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86668109929033961253702065 65001082446775470940276549)
            ·
              refine ⟨12187702958770400801301853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65001082446775470940276549 12187702958770400801301853)
              ·
                refine ⟨4570388609538900300488195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12187702958770400801301853 4570388609538900300488195)
                ·
                  refine ⟨6855582914308350450732293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570388609538900300488195 6855582914308350450732293)
                  ·
                    refine ⟨1285421796432815709512305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6855582914308350450732293 1285421796432815709512305)
                    ·
                      rfl

theorem cell23_7510050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_7510050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510050 prefixEnd_7510050 := by exact prefixLift 7510050
  have htrace : WordTrace (prefixWord ++ tailWord_7510050) baseStart_7510050 baseEnd_7510050 := by
    simpa [prefixWord, tailWord_7510050, baseEnd_7510050] using wordTrace_append hprefix tailTrace_7510050
  have hstable : (prefixWord ++ tailWord_7510050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510050).length < 2 ^ (prefixWord ++ tailWord_7510050).sum := by decide
  have hdescent : baseEnd_7510050 < baseStart_7510050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510059 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 5, 5]
def baseStart_7510059 : Nat := 118140960795 + 7510059 * 2 ^ 59
def prefixEnd_7510059 : Nat := 4983230072969 + 3 ^ 40 * 7510059 * 2
def baseEnd_7510059 : Nat := 1285423336874779197774791

theorem tailTrace_7510059 : CollatzResearch.WordTrace tailWord_7510059 prefixEnd_7510059 1285423336874779197774791 := by
  unfold tailWord_7510059
  simp only [CollatzResearch.WordTrace]
  refine ⟨273914354699346333808037231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182609569799564222538691487 273914354699346333808037231)
  ·
    refine ⟨410871532049019500712055847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273914354699346333808037231 410871532049019500712055847)
    ·
      refine ⟨616307298073529251068083771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410871532049019500712055847 616307298073529251068083771)
      ·
        refine ⟨924460947110293876602125657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616307298073529251068083771 924460947110293876602125657)
        ·
          refine ⟨693345710332720407451594243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924460947110293876602125657 693345710332720407451594243)
          ·
            refine ⟨1040018565499080611177391365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693345710332720407451594243 1040018565499080611177391365)
            ·
              refine ⟨195003481031077614595760881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1040018565499080611177391365 195003481031077614595760881)
              ·
                refine ⟨146252610773308210946820661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195003481031077614595760881 146252610773308210946820661)
                ·
                  refine ⟨13711182259997644776264437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146252610773308210946820661 13711182259997644776264437)
                  ·
                    refine ⟨1285423336874779197774791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13711182259997644776264437 1285423336874779197774791)
                    ·
                      rfl

theorem cell23_7510059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 5].length) (baseStart_7510059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510059 prefixEnd_7510059 := by exact prefixLift 7510059
  have htrace : WordTrace (prefixWord ++ tailWord_7510059) baseStart_7510059 baseEnd_7510059 := by
    simpa [prefixWord, tailWord_7510059, baseEnd_7510059] using wordTrace_append hprefix tailTrace_7510059
  have hstable : (prefixWord ++ tailWord_7510059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510059).length < 2 ^ (prefixWord ++ tailWord_7510059).sum := by decide
  have hdescent : baseEnd_7510059 < baseStart_7510059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510106 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_7510106 : Nat := 118140960795 + 7510106 * 2 ^ 59
def prefixEnd_7510106 : Nat := 4983230072969 + 3 ^ 40 * 7510106 * 2
def baseEnd_7510106 : Nat := 1285431381405032969812219

theorem tailTrace_7510106 : CollatzResearch.WordTrace tailWord_7510106 prefixEnd_7510106 1285431381405032969812219 := by
  unfold tailWord_7510106
  simp only [CollatzResearch.WordTrace]
  refine ⟨68479017232544015208749543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182610712620117373889998781 68479017232544015208749543)
  ·
    refine ⟨102718525848816022813124315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68479017232544015208749543 102718525848816022813124315)
    ·
      refine ⟨154077788773224034219686473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102718525848816022813124315 154077788773224034219686473)
      ·
        refine ⟨115558341579918025664764855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154077788773224034219686473 115558341579918025664764855)
        ·
          refine ⟨173337512369877038497147283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115558341579918025664764855 173337512369877038497147283)
          ·
            refine ⟨260006268554815557745720925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173337512369877038497147283 260006268554815557745720925)
            ·
              refine ⟨97502350708055834154645347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260006268554815557745720925 97502350708055834154645347)
              ·
                refine ⟨146253526062083751231968021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97502350708055834154645347 146253526062083751231968021)
                ·
                  refine ⟨6855634034160175838998501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146253526062083751231968021 6855634034160175838998501)
                  ·
                    refine ⟨1285431381405032969812219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6855634034160175838998501 1285431381405032969812219)
                    ·
                      rfl

theorem cell23_7510106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_7510106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510106 prefixEnd_7510106 := by exact prefixLift 7510106
  have htrace : WordTrace (prefixWord ++ tailWord_7510106) baseStart_7510106 baseEnd_7510106 := by
    simpa [prefixWord, tailWord_7510106, baseEnd_7510106] using wordTrace_append hprefix tailTrace_7510106
  have hstable : (prefixWord ++ tailWord_7510106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510106).length < 2 ^ (prefixWord ++ tailWord_7510106).sum := by decide
  have hdescent : baseEnd_7510106 < baseStart_7510106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510116 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_7510116 : Nat := 118140960795 + 7510116 * 2 ^ 59
def prefixEnd_7510116 : Nat := 4983230072969 + 3 ^ 40 * 7510116 * 2
def baseEnd_7510116 : Nat := 3856299279021643870311611

theorem tailTrace_7510116 : CollatzResearch.WordTrace tailWord_7510116 prefixEnd_7510116 3856299279021643870311611 := by
  unfold tailWord_7510116
  simp only [CollatzResearch.WordTrace]
  refine ⟨136958216830069916271431101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182610955773426555028574801 136958216830069916271431101)
  ·
    refine ⟨51359331311276218601786663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136958216830069916271431101 51359331311276218601786663)
    ·
      refine ⟨77038996966914327902679995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51359331311276218601786663 77038996966914327902679995)
      ·
        refine ⟨115558495450371491854019993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77038996966914327902679995 115558495450371491854019993)
        ·
          refine ⟨86668871587778618890514995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115558495450371491854019993 86668871587778618890514995)
          ·
            refine ⟨130003307381667928335772493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86668871587778618890514995 130003307381667928335772493)
            ·
              refine ⟨48751240268125473125914685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130003307381667928335772493 48751240268125473125914685)
              ·
                refine ⟨18281715100547052422218007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48751240268125473125914685 18281715100547052422218007)
                ·
                  refine ⟨27422572650820578633327011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18281715100547052422218007 27422572650820578633327011)
                  ·
                    refine ⟨41133858976230867949990517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27422572650820578633327011 41133858976230867949990517)
                    ·
                      refine ⟨3856299279021643870311611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41133858976230867949990517 3856299279021643870311611)
                      ·
                        rfl

theorem cell23_7510116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_7510116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510116 prefixEnd_7510116 := by exact prefixLift 7510116
  have htrace : WordTrace (prefixWord ++ tailWord_7510116) baseStart_7510116 baseEnd_7510116 := by
    simpa [prefixWord, tailWord_7510116, baseEnd_7510116] using wordTrace_append hprefix tailTrace_7510116
  have hstable : (prefixWord ++ tailWord_7510116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510116).length < 2 ^ (prefixWord ++ tailWord_7510116).sum := by decide
  have hdescent : baseEnd_7510116 < baseStart_7510116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510126 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_7510126 : Nat := 118140960795 + 7510126 * 2 ^ 59
def prefixEnd_7510126 : Nat := 4983230072969 + 3 ^ 40 * 7510126 * 2
def baseEnd_7510126 : Nat := 3856304413828188831186565

theorem tailTrace_7510126 : CollatzResearch.WordTrace tailWord_7510126 prefixEnd_7510126 3856304413828188831186565 := by
  unfold tailWord_7510126
  simp only [CollatzResearch.WordTrace]
  refine ⟨34239599798762950531340779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182611198926735736167150821 34239599798762950531340779)
  ·
    refine ⟨51359399698144425797011169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34239599798762950531340779 51359399698144425797011169)
    ·
      refine ⟨38519549773608319347758377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51359399698144425797011169 38519549773608319347758377)
      ·
        refine ⟨28889662330206239510818783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38519549773608319347758377 28889662330206239510818783)
        ·
          refine ⟨43334493495309359266228175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28889662330206239510818783 43334493495309359266228175)
          ·
            refine ⟨65001740242964038899342263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43334493495309359266228175 65001740242964038899342263)
            ·
              refine ⟨97502610364446058349013395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65001740242964038899342263 97502610364446058349013395)
              ·
                refine ⟨146253915546669087523520093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97502610364446058349013395 146253915546669087523520093)
                ·
                  refine ⟨54845218330000907821320035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146253915546669087523520093 54845218330000907821320035)
                  ·
                    refine ⟨82267827495001361731980053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54845218330000907821320035 82267827495001361731980053)
                    ·
                      refine ⟨3856304413828188831186565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82267827495001361731980053 3856304413828188831186565)
                      ·
                        rfl

theorem cell23_7510126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_7510126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510126 prefixEnd_7510126 := by exact prefixLift 7510126
  have htrace : WordTrace (prefixWord ++ tailWord_7510126) baseStart_7510126 baseEnd_7510126 := by
    simpa [prefixWord, tailWord_7510126, baseEnd_7510126] using wordTrace_append hprefix tailTrace_7510126
  have hstable : (prefixWord ++ tailWord_7510126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510126).length < 2 ^ (prefixWord ++ tailWord_7510126).sum := by decide
  have hdescent : baseEnd_7510126 < baseStart_7510126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510140 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_7510140 : Nat := 118140960795 + 7510140 * 2 ^ 59
def prefixEnd_7510140 : Nat := 4983230072969 + 3 ^ 40 * 7510140 * 2
def baseEnd_7510140 : Nat := 1285437200852450592137167

theorem tailTrace_7510140 : CollatzResearch.WordTrace tailWord_7510140 prefixEnd_7510140 1285437200852450592137167 := by
  unfold tailWord_7510140
  simp only [CollatzResearch.WordTrace]
  refine ⟨136958654506026442320867937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182611539341368589761157249 136958654506026442320867937)
  ·
    refine ⟨102718990879519831740650953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136958654506026442320867937 102718990879519831740650953)
    ·
      refine ⟨77039243159639873805488215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102718990879519831740650953 77039243159639873805488215)
      ·
        refine ⟨115558864739459810708232323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77039243159639873805488215 115558864739459810708232323)
        ·
          refine ⟨173338297109189716062348485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115558864739459810708232323 173338297109189716062348485)
          ·
            refine ⟨32500930707973071761690341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173338297109189716062348485 32500930707973071761690341)
            ·
              refine ⟨6093924507744950955316939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32500930707973071761690341 6093924507744950955316939)
              ·
                refine ⟨9140886761617426432975409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093924507744950955316939 9140886761617426432975409)
                ·
                  refine ⟨6855665071213069824731557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9140886761617426432975409 6855665071213069824731557)
                  ·
                    refine ⟨1285437200852450592137167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6855665071213069824731557 1285437200852450592137167)
                    ·
                      rfl

theorem cell23_7510140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_7510140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510140 prefixEnd_7510140 := by exact prefixLift 7510140
  have htrace : WordTrace (prefixWord ++ tailWord_7510140) baseStart_7510140 baseEnd_7510140 := by
    simpa [prefixWord, tailWord_7510140, baseEnd_7510140] using wordTrace_append hprefix tailTrace_7510140
  have hstable : (prefixWord ++ tailWord_7510140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510140).length < 2 ^ (prefixWord ++ tailWord_7510140).sum := by decide
  have hdescent : baseEnd_7510140 < baseStart_7510140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510164 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7510164 : Nat := 118140960795 + 7510164 * 2 ^ 59
def prefixEnd_7510164 : Nat := 4983230072969 + 3 ^ 40 * 7510164 * 2
def baseEnd_7510164 : Nat := 3856323926093059682511391

theorem tailTrace_7510164 : CollatzResearch.WordTrace tailWord_7510164 prefixEnd_7510164 3856323926093059682511391 := by
  unfold tailWord_7510164
  simp only [CollatzResearch.WordTrace]
  refine ⟨136959092181982968370304773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182612122909310624493739697 136959092181982968370304773)
  ·
    refine ⟨25679829784121806569432145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136959092181982968370304773 25679829784121806569432145)
    ·
      refine ⟨19259872338091354927074109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25679829784121806569432145 19259872338091354927074109)
      ·
        refine ⟨7222452126784258097652791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19259872338091354927074109 7222452126784258097652791)
        ·
          refine ⟨10833678190176387146479187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222452126784258097652791 10833678190176387146479187)
          ·
            refine ⟨16250517285264580719718781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833678190176387146479187 16250517285264580719718781)
            ·
              refine ⟨6093943981974217769894543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16250517285264580719718781 6093943981974217769894543)
              ·
                refine ⟨9140915972961326654841815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093943981974217769894543 9140915972961326654841815)
                ·
                  refine ⟨13711373959441989982262723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9140915972961326654841815 13711373959441989982262723)
                  ·
                    refine ⟨20567060939162984973394085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13711373959441989982262723 20567060939162984973394085)
                    ·
                      refine ⟨3856323926093059682511391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20567060939162984973394085 3856323926093059682511391)
                      ·
                        rfl

theorem cell23_7510164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7510164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510164 prefixEnd_7510164 := by exact prefixLift 7510164
  have htrace : WordTrace (prefixWord ++ tailWord_7510164) baseStart_7510164 baseEnd_7510164 := by
    simpa [prefixWord, tailWord_7510164, baseEnd_7510164] using wordTrace_append hprefix tailTrace_7510164
  have hstable : (prefixWord ++ tailWord_7510164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510164).length < 2 ^ (prefixWord ++ tailWord_7510164).sum := by decide
  have hdescent : baseEnd_7510164 < baseStart_7510164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510167 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 1, 2, 3]
def baseStart_7510167 : Nat := 118140960795 + 7510167 * 2 ^ 59
def prefixEnd_7510167 : Nat := 4983230072969 + 3 ^ 40 * 7510167 * 2
def baseEnd_7510167 : Nat := 3856325466535023170773877

theorem tailTrace_7510167 : CollatzResearch.WordTrace tailWord_7510167 prefixEnd_7510167 3856325466535023170773877 := by
  unfold tailWord_7510167
  simp only [CollatzResearch.WordTrace]
  refine ⟨273918293782955068252968755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182612195855303378835312503 273918293782955068252968755)
  ·
    refine ⟨410877440674432602379453133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273918293782955068252968755 410877440674432602379453133)
    ·
      refine ⟨154079040252912225892294925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410877440674432602379453133 154079040252912225892294925)
      ·
        refine ⟨57779640094842084709610597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154079040252912225892294925 57779640094842084709610597)
        ·
          refine ⟨10833682517782890883051987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57779640094842084709610597 10833682517782890883051987)
          ·
            refine ⟨16250523776674336324577981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833682517782890883051987 16250523776674336324577981)
            ·
              refine ⟨6093946416252876121716743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16250523776674336324577981 6093946416252876121716743)
              ·
                refine ⟨9140919624379314182575115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093946416252876121716743 9140919624379314182575115)
                ·
                  refine ⟨13711379436568971273862673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9140919624379314182575115 13711379436568971273862673)
                  ·
                    refine ⟨10283534577426728455397005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13711379436568971273862673 10283534577426728455397005)
                    ·
                      refine ⟨3856325466535023170773877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10283534577426728455397005 3856325466535023170773877)
                      ·
                        rfl

theorem cell23_7510167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_7510167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510167 prefixEnd_7510167 := by exact prefixLift 7510167
  have htrace : WordTrace (prefixWord ++ tailWord_7510167) baseStart_7510167 baseEnd_7510167 := by
    simpa [prefixWord, tailWord_7510167, baseEnd_7510167] using wordTrace_append hprefix tailTrace_7510167
  have hstable : (prefixWord ++ tailWord_7510167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510167).length < 2 ^ (prefixWord ++ tailWord_7510167).sum := by decide
  have hdescent : baseEnd_7510167 < baseStart_7510167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510197 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_7510197 : Nat := 118140960795 + 7510197 * 2 ^ 59
def prefixEnd_7510197 : Nat := 4983230072969 + 3 ^ 40 * 7510197 * 2
def baseEnd_7510197 : Nat := 3856340870954658053398739

theorem tailTrace_7510197 : CollatzResearch.WordTrace tailWord_7510197 prefixEnd_7510197 3856340870954658053398739 := by
  unfold tailWord_7510197
  simp only [CollatzResearch.WordTrace]
  refine ⟨273919387972846383376560845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182612925315230922251040563 273919387972846383376560845)
  ·
    refine ⟨102719770489817393766210317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273919387972846383376560845 102719770489817393766210317)
    ·
      refine ⟨38519913933681522662328869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102719770489817393766210317 38519913933681522662328869)
      ·
        refine ⟨7222483862565285499186663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38519913933681522662328869 7222483862565285499186663)
        ·
          refine ⟨10833725793847928248779995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222483862565285499186663 10833725793847928248779995)
          ·
            refine ⟨16250588690771892373169993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833725793847928248779995 16250588690771892373169993)
            ·
              refine ⟨12187941518078919279877495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16250588690771892373169993 12187941518078919279877495)
              ·
                refine ⟨18281912277118378919816243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12187941518078919279877495 18281912277118378919816243)
                ·
                  refine ⟨27422868415677568379724365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18281912277118378919816243 27422868415677568379724365)
                  ·
                    refine ⟨10283575655879088142396637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27422868415677568379724365 10283575655879088142396637)
                    ·
                      refine ⟨3856340870954658053398739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10283575655879088142396637 3856340870954658053398739)
                      ·
                        rfl

theorem cell23_7510197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_7510197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510197 prefixEnd_7510197 := by exact prefixLift 7510197
  have htrace : WordTrace (prefixWord ++ tailWord_7510197) baseStart_7510197 baseEnd_7510197 := by
    simpa [prefixWord, tailWord_7510197, baseEnd_7510197] using wordTrace_append hprefix tailTrace_7510197
  have hstable : (prefixWord ++ tailWord_7510197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510197).length < 2 ^ (prefixWord ++ tailWord_7510197).sum := by decide
  have hdescent : baseEnd_7510197 < baseStart_7510197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510216 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_7510216 : Nat := 118140960795 + 7510216 * 2 ^ 59
def prefixEnd_7510216 : Nat := 4983230072969 + 3 ^ 40 * 7510216 * 2
def baseEnd_7510216 : Nat := 3856350627087093479061151

theorem tailTrace_7510216 : CollatzResearch.WordTrace tailWord_7510216 prefixEnd_7510216 3856350627087093479061151 := by
  unfold tailWord_7510216
  simp only [CollatzResearch.WordTrace]
  refine ⟨136960040479888774810751251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182613387306518366414335001 136960040479888774810751251)
  ·
    refine ⟨205440060719833162216126877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136960040479888774810751251 205440060719833162216126877)
    ·
      refine ⟨77040022769937435831047579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205440060719833162216126877 77040022769937435831047579)
      ·
        refine ⟨115560034154906153746571369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77040022769937435831047579 115560034154906153746571369)
        ·
          refine ⟨86670025616179615309928527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115560034154906153746571369 86670025616179615309928527)
          ·
            refine ⟨130005038424269422964892791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86670025616179615309928527 130005038424269422964892791)
            ·
              refine ⟨195007557636404134447339187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130005038424269422964892791 195007557636404134447339187)
              ·
                refine ⟨292511336454606201671008781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195007557636404134447339187 292511336454606201671008781)
                ·
                  refine ⟨109691751170477325626628293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292511336454606201671008781 109691751170477325626628293)
                  ·
                    refine ⟨20567203344464498554992805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109691751170477325626628293 20567203344464498554992805)
                    ·
                      refine ⟨3856350627087093479061151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20567203344464498554992805 3856350627087093479061151)
                      ·
                        rfl

theorem cell23_7510216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_7510216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510216 prefixEnd_7510216 := by exact prefixLift 7510216
  have htrace : WordTrace (prefixWord ++ tailWord_7510216) baseStart_7510216 baseEnd_7510216 := by
    simpa [prefixWord, tailWord_7510216, baseEnd_7510216] using wordTrace_append hprefix tailTrace_7510216
  have hstable : (prefixWord ++ tailWord_7510216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510216).length < 2 ^ (prefixWord ++ tailWord_7510216).sum := by decide
  have hdescent : baseEnd_7510216 < baseStart_7510216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510230 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_7510230 : Nat := 118140960795 + 7510230 * 2 ^ 59
def prefixEnd_7510230 : Nat := 4983230072969 + 3 ^ 40 * 7510230 * 2
def baseEnd_7510230 : Nat := 1285452605272085474762029

theorem tailTrace_7510230 : CollatzResearch.WordTrace tailWord_7510230 prefixEnd_7510230 1285452605272085474762029 := by
  unfold tailWord_7510230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17120036973857926875782009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182613727721151220008341429 17120036973857926875782009)
  ·
    refine ⟨12840027730393445156836507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17120036973857926875782009 12840027730393445156836507)
    ·
      refine ⟨19260041595590167735254761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12840027730393445156836507 19260041595590167735254761)
      ·
        refine ⟨14445031196692625801441071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19260041595590167735254761 14445031196692625801441071)
        ·
          refine ⟨21667546795038938702161607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14445031196692625801441071 21667546795038938702161607)
          ·
            refine ⟨32501320192558408053242411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21667546795038938702161607 32501320192558408053242411)
            ·
              refine ⟨48751980288837612079863617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32501320192558408053242411 48751980288837612079863617)
              ·
                refine ⟨36563985216628209059897713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48751980288837612079863617 36563985216628209059897713)
                ·
                  refine ⟨27422988912471156794923285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36563985216628209059897713 27422988912471156794923285)
                  ·
                    refine ⟨1285452605272085474762029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27422988912471156794923285 1285452605272085474762029)
                    ·
                      rfl

theorem cell23_7510230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_7510230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510230 prefixEnd_7510230 := by exact prefixLift 7510230
  have htrace : WordTrace (prefixWord ++ tailWord_7510230) baseStart_7510230 baseEnd_7510230 := by
    simpa [prefixWord, tailWord_7510230, baseEnd_7510230] using wordTrace_append hprefix tailTrace_7510230
  have hstable : (prefixWord ++ tailWord_7510230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510230).length < 2 ^ (prefixWord ++ tailWord_7510230).sum := by decide
  have hdescent : baseEnd_7510230 < baseStart_7510230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510273 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 2, 5]
def baseStart_7510273 : Nat := 118140960795 + 7510273 * 2 ^ 59
def prefixEnd_7510273 : Nat := 4983230072969 + 3 ^ 40 * 7510273 * 2
def baseEnd_7510273 : Nat := 1285459965161466585349463

theorem tailTrace_7510273 : CollatzResearch.WordTrace tailWord_7510273 prefixEnd_7510273 1285459965161466585349463 := by
  unfold tailWord_7510273
  simp only [CollatzResearch.WordTrace]
  refine ⟨273922159920571048356327473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182614773280380698904218315 273922159920571048356327473)
  ·
    refine ⟨205441619940428286267245605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273922159920571048356327473 205441619940428286267245605)
    ·
      refine ⟨38520303738830303675108551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205441619940428286267245605 38520303738830303675108551)
      ·
        refine ⟨57780455608245455512662827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38520303738830303675108551 57780455608245455512662827)
        ·
          refine ⟨86670683412368183268994241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57780455608245455512662827 86670683412368183268994241)
          ·
            refine ⟨65003012559276137451745681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86670683412368183268994241 65003012559276137451745681)
            ·
              refine ⟨48752259419457103088809261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65003012559276137451745681 48752259419457103088809261)
              ·
                refine ⟨18282097282296413658303473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48752259419457103088809261 18282097282296413658303473)
                ·
                  refine ⟨13711572961722310243727605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18282097282296413658303473 13711572961722310243727605)
                  ·
                    refine ⟨1285459965161466585349463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13711572961722310243727605 1285459965161466585349463)
                    ·
                      rfl

theorem cell23_7510273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_7510273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510273 prefixEnd_7510273 := by exact prefixLift 7510273
  have htrace : WordTrace (prefixWord ++ tailWord_7510273) baseStart_7510273 baseEnd_7510273 := by
    simpa [prefixWord, tailWord_7510273, baseEnd_7510273] using wordTrace_append hprefix tailTrace_7510273
  have hstable : (prefixWord ++ tailWord_7510273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510273).length < 2 ^ (prefixWord ++ tailWord_7510273).sum := by decide
  have hdescent : baseEnd_7510273 < baseStart_7510273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510293 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_7510293 : Nat := 118140960795 + 7510293 * 2 ^ 59
def prefixEnd_7510293 : Nat := 4983230072969 + 3 ^ 40 * 7510293 * 2
def baseEnd_7510293 : Nat := 3856390165097489677798297

theorem tailTrace_7510293 : CollatzResearch.WordTrace tailWord_7510293 prefixEnd_7510293 3856390165097489677798297 := by
  unfold tailWord_7510293
  simp only [CollatzResearch.WordTrace]
  refine ⟨273922889380498591772055533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182615259586999061181370355 273922889380498591772055533)
  ·
    refine ⟨102721083517686971914520825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273922889380498591772055533 102721083517686971914520825)
    ·
      refine ⟨77040812638265228935890619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102721083517686971914520825 77040812638265228935890619)
      ·
        refine ⟨115561218957397843403835929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77040812638265228935890619 115561218957397843403835929)
        ·
          refine ⟨86670914218048382552876947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115561218957397843403835929 86670914218048382552876947)
          ·
            refine ⟨130006371327072573829315421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86670914218048382552876947 130006371327072573829315421)
            ·
              refine ⟨48752389247652215185993283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130006371327072573829315421 48752389247652215185993283)
              ·
                refine ⟨73128583871478322778989925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48752389247652215185993283 73128583871478322778989925)
                ·
                  refine ⟨13711609475902185521060611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73128583871478322778989925 13711609475902185521060611)
                  ·
                    refine ⟨20567414213853278281590917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13711609475902185521060611 20567414213853278281590917)
                    ·
                      refine ⟨3856390165097489677798297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20567414213853278281590917 3856390165097489677798297)
                      ·
                        rfl

theorem cell23_7510293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_7510293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510293 prefixEnd_7510293 := by exact prefixLift 7510293
  have htrace : WordTrace (prefixWord ++ tailWord_7510293) baseStart_7510293 baseEnd_7510293 := by
    simpa [prefixWord, tailWord_7510293, baseEnd_7510293] using wordTrace_append hprefix tailTrace_7510293
  have hstable : (prefixWord ++ tailWord_7510293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510293).length < 2 ^ (prefixWord ++ tailWord_7510293).sum := by decide
  have hdescent : baseEnd_7510293 < baseStart_7510293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510330 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3]
def baseStart_7510330 : Nat := 118140960795 + 7510330 * 2 ^ 59
def prefixEnd_7510330 : Nat := 4983230072969 + 3 ^ 40 * 7510330 * 2
def baseEnd_7510330 : Nat := 3856409163881706033035627

theorem tailTrace_7510330 : CollatzResearch.WordTrace tailWord_7510330 prefixEnd_7510330 3856409163881706033035627 := by
  unfold tailWord_7510330
  simp only [CollatzResearch.WordTrace]
  refine ⟨68481059720341136772788111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182616159254243031394101629 68481059720341136772788111)
  ·
    refine ⟨102721589580511705159182167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68481059720341136772788111 102721589580511705159182167)
    ·
      refine ⟨154082384370767557738773251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102721589580511705159182167 154082384370767557738773251)
      ·
        refine ⟨231123576556151336608159877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154082384370767557738773251 231123576556151336608159877)
        ·
          refine ⟨43335670604278375614029977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231123576556151336608159877 43335670604278375614029977)
          ·
            refine ⟨32501752953208781710522483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43335670604278375614029977 32501752953208781710522483)
            ·
              refine ⟨48752629429813172565783725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32501752953208781710522483 48752629429813172565783725)
              ·
                refine ⟨18282236036179939712168897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48752629429813172565783725 18282236036179939712168897)
                ·
                  refine ⟨13711677027134954784126673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18282236036179939712168897 13711677027134954784126673)
                  ·
                    refine ⟨10283757770351216088095005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13711677027134954784126673 10283757770351216088095005)
                    ·
                      refine ⟨3856409163881706033035627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10283757770351216088095005 3856409163881706033035627)
                      ·
                        rfl

theorem cell23_7510330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_7510330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510330 prefixEnd_7510330 := by exact prefixLift 7510330
  have htrace : WordTrace (prefixWord ++ tailWord_7510330) baseStart_7510330 baseEnd_7510330 := by
    simpa [prefixWord, tailWord_7510330, baseEnd_7510330] using wordTrace_append hprefix tailTrace_7510330
  have hstable : (prefixWord ++ tailWord_7510330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510330).length < 2 ^ (prefixWord ++ tailWord_7510330).sum := by decide
  have hdescent : baseEnd_7510330 < baseStart_7510330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510354 : List Nat := [3, 2, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_7510354 : Nat := 118140960795 + 7510354 * 2 ^ 59
def prefixEnd_7510354 : Nat := 4983230072969 + 3 ^ 40 * 7510354 * 2
def baseEnd_7510354 : Nat := 1285473829139137979711839

theorem tailTrace_7510354 : CollatzResearch.WordTrace tailWord_7510354 prefixEnd_7510354 1285473829139137979711839 := by
  unfold tailWord_7510354
  simp only [CollatzResearch.WordTrace]
  refine ⟨68481278558319399797506529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182616742822185066126684077 68481278558319399797506529)
  ·
    refine ⟨51360958918739549848129897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68481278558319399797506529 51360958918739549848129897)
    ·
      refine ⟨38520719189054662386097423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51360958918739549848129897 38520719189054662386097423)
      ·
        refine ⟨57781078783581993579146135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38520719189054662386097423 57781078783581993579146135)
        ·
          refine ⟨86671618175372990368719203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57781078783581993579146135 86671618175372990368719203)
          ·
            refine ⟨130007427263059485553078805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86671618175372990368719203 130007427263059485553078805)
            ·
              refine ⟨6094098152955913385300569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130007427263059485553078805 6094098152955913385300569)
              ·
                refine ⟨4570573614716935038975427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6094098152955913385300569 4570573614716935038975427)
                ·
                  refine ⟨6855860422075402558463141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570573614716935038975427 6855860422075402558463141)
                  ·
                    refine ⟨1285473829139137979711839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6855860422075402558463141 1285473829139137979711839)
                    ·
                      rfl

theorem cell23_7510354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_7510354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510354 prefixEnd_7510354 := by exact prefixLift 7510354
  have htrace : WordTrace (prefixWord ++ tailWord_7510354) baseStart_7510354 baseEnd_7510354 := by
    simpa [prefixWord, tailWord_7510354, baseEnd_7510354] using wordTrace_append hprefix tailTrace_7510354
  have hstable : (prefixWord ++ tailWord_7510354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510354).length < 2 ^ (prefixWord ++ tailWord_7510354).sum := by decide
  have hdescent : baseEnd_7510354 < baseStart_7510354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510397 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 1, 5]
def baseStart_7510397 : Nat := 118140960795 + 7510397 * 2 ^ 59
def prefixEnd_7510397 : Nat := 4983230072969 + 3 ^ 40 * 7510397 * 2
def baseEnd_7510397 : Nat := 1285481189028519090299273

theorem tailTrace_7510397 : CollatzResearch.WordTrace tailWord_7510397 prefixEnd_7510397 1285481189028519090299273 := by
  unfold tailWord_7510397
  simp only [CollatzResearch.WordTrace]
  refine ⟨273926682572121817533841445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182617788381414545022560963 273926682572121817533841445)
  ·
    refine ⟨51361252982272840787595271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273926682572121817533841445 51361252982272840787595271)
    ·
      refine ⟨77041879473409261181392907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51361252982272840787595271 77041879473409261181392907)
      ·
        refine ⟨115562819210113891772089361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77041879473409261181392907 115562819210113891772089361)
        ·
          refine ⟨86672114407585418829067021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115562819210113891772089361 86672114407585418829067021)
          ·
            refine ⟨32502042902844532060900133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86672114407585418829067021 32502042902844532060900133)
            ·
              refine ⟨6094133044283349761418775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32502042902844532060900133 6094133044283349761418775)
              ·
                refine ⟨9141199566425024642128163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094133044283349761418775 9141199566425024642128163)
                ·
                  refine ⟨13711799349637536963192245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9141199566425024642128163 13711799349637536963192245)
                  ·
                    refine ⟨1285481189028519090299273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13711799349637536963192245 1285481189028519090299273)
                    ·
                      rfl

theorem cell23_7510397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_7510397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510397 prefixEnd_7510397 := by exact prefixLift 7510397
  have htrace : WordTrace (prefixWord ++ tailWord_7510397) baseStart_7510397 baseEnd_7510397 := by
    simpa [prefixWord, tailWord_7510397, baseEnd_7510397] using wordTrace_append hprefix tailTrace_7510397
  have hstable : (prefixWord ++ tailWord_7510397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510397).length < 2 ^ (prefixWord ++ tailWord_7510397).sum := by decide
  have hdescent : baseEnd_7510397 < baseStart_7510397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510434 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_7510434 : Nat := 118140960795 + 7510434 * 2 ^ 59
def prefixEnd_7510434 : Nat := 4983230072969 + 3 ^ 40 * 7510434 * 2
def baseEnd_7510434 : Nat := 3856462565869773626135149

theorem tailTrace_7510434 : CollatzResearch.WordTrace tailWord_7510434 prefixEnd_7510434 3856462565869773626135149 := by
  unfold tailWord_7510434
  simp only [CollatzResearch.WordTrace]
  refine ⟨68482008018246943213234589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182618688048658515235292237 68482008018246943213234589)
  ·
    refine ⟨25680753006842603704962971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68482008018246943213234589 25680753006842603704962971)
    ·
      refine ⟨38521129510263905557444457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25680753006842603704962971 38521129510263905557444457)
      ·
        refine ⟨28890847132697929168083343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38521129510263905557444457 28890847132697929168083343)
        ·
          refine ⟨43336270699046893752125015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28890847132697929168083343 43336270699046893752125015)
          ·
            refine ⟨65004406048570340628187523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43336270699046893752125015 65004406048570340628187523)
            ·
              refine ⟨97506609072855510942281285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65004406048570340628187523 97506609072855510942281285)
              ·
                refine ⟨18282489201160408301677741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97506609072855510942281285 18282489201160408301677741)
                ·
                  refine ⟨6855933450435153113129153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18282489201160408301677741 6855933450435153113129153)
                  ·
                    refine ⟨5141950087826364834846865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6855933450435153113129153 5141950087826364834846865)
                    ·
                      refine ⟨3856462565869773626135149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5141950087826364834846865 3856462565869773626135149)
                      ·
                        rfl

theorem cell23_7510434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_7510434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510434 prefixEnd_7510434 := by exact prefixLift 7510434
  have htrace : WordTrace (prefixWord ++ tailWord_7510434) baseStart_7510434 baseEnd_7510434 := by
    simpa [prefixWord, tailWord_7510434, baseEnd_7510434] using wordTrace_append hprefix tailTrace_7510434
  have hstable : (prefixWord ++ tailWord_7510434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510434).length < 2 ^ (prefixWord ++ tailWord_7510434).sum := by decide
  have hdescent : baseEnd_7510434 < baseStart_7510434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510437 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 3]
def baseStart_7510437 : Nat := 118140960795 + 7510437 * 2 ^ 59
def prefixEnd_7510437 : Nat := 4983230072969 + 3 ^ 40 * 7510437 * 2
def baseEnd_7510437 : Nat := 3856464106311737114397635

theorem tailTrace_7510437 : CollatzResearch.WordTrace tailWord_7510437 prefixEnd_7510437 3856464106311737114397635 := by
  unfold tailWord_7510437
  simp only [CollatzResearch.WordTrace]
  refine ⟨273928141491976904365297565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182618760994651269576865043 273928141491976904365297565)
  ·
    refine ⟨102723053059491339136986587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273928141491976904365297565 102723053059491339136986587)
    ·
      refine ⟨154084579589237008705479881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102723053059491339136986587 154084579589237008705479881)
      ·
        refine ⟨115563434691927756529109911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154084579589237008705479881 115563434691927756529109911)
        ·
          refine ⟨173345152037891634793664867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115563434691927756529109911 173345152037891634793664867)
          ·
            refine ⟨260017728056837452190497301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173345152037891634793664867 260017728056837452190497301)
            ·
              refine ⟨12188331002664255571429561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260017728056837452190497301 12188331002664255571429561)
              ·
                refine ⟨9141248251998191678572171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12188331002664255571429561 9141248251998191678572171)
                ·
                  refine ⟨13711872377997287517858257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9141248251998191678572171 13711872377997287517858257)
                  ·
                    refine ⟨10283904283497965638393693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13711872377997287517858257 10283904283497965638393693)
                    ·
                      refine ⟨3856464106311737114397635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10283904283497965638393693 3856464106311737114397635)
                      ·
                        rfl

theorem cell23_7510437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_7510437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510437 prefixEnd_7510437 := by exact prefixLift 7510437
  have htrace : WordTrace (prefixWord ++ tailWord_7510437) baseStart_7510437 baseEnd_7510437 := by
    simpa [prefixWord, tailWord_7510437, baseEnd_7510437] using wordTrace_append hprefix tailTrace_7510437
  have hstable : (prefixWord ++ tailWord_7510437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510437).length < 2 ^ (prefixWord ++ tailWord_7510437).sum := by decide
  have hdescent : baseEnd_7510437 < baseStart_7510437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510445 : List Nat := [1, 5, 2, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7510445 : Nat := 118140960795 + 7510445 * 2 ^ 59
def prefixEnd_7510445 : Nat := 4983230072969 + 3 ^ 40 * 7510445 * 2
def baseEnd_7510445 : Nat := 3856468214156973083097599

theorem tailTrace_7510445 : CollatzResearch.WordTrace tailWord_7510445 prefixEnd_7510445 3856468214156973083097599 := by
  unfold tailWord_7510445
  simp only [CollatzResearch.WordTrace]
  refine ⟨273928433275947921731588789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182618955517298614487725859 273928433275947921731588789)
  ·
    refine ⟨25680790619620117662336449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273928433275947921731588789 25680790619620117662336449)
    ·
      refine ⟨19260592964715088246752337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25680790619620117662336449 19260592964715088246752337)
      ·
        refine ⟨14445444723536316185064253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19260592964715088246752337 14445444723536316185064253)
        ·
          refine ⟨5417041771326118569399095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14445444723536316185064253 5417041771326118569399095)
          ·
            refine ⟨8125562656989177854098643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417041771326118569399095 8125562656989177854098643)
            ·
              refine ⟨12188343985483766781147965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125562656989177854098643 12188343985483766781147965)
              ·
                refine ⟨4570628994556412542930487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12188343985483766781147965 4570628994556412542930487)
                ·
                  refine ⟨6855943491834618814395731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570628994556412542930487 6855943491834618814395731)
                  ·
                    refine ⟨10283915237751928221593597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6855943491834618814395731 10283915237751928221593597)
                    ·
                      refine ⟨3856468214156973083097599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10283915237751928221593597 3856468214156973083097599)
                      ·
                        rfl

theorem cell23_7510445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7510445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510445 prefixEnd_7510445 := by exact prefixLift 7510445
  have htrace : WordTrace (prefixWord ++ tailWord_7510445) baseStart_7510445 baseEnd_7510445 := by
    simpa [prefixWord, tailWord_7510445, baseEnd_7510445] using wordTrace_append hprefix tailTrace_7510445
  have hstable : (prefixWord ++ tailWord_7510445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510445).length < 2 ^ (prefixWord ++ tailWord_7510445).sum := by decide
  have hdescent : baseEnd_7510445 < baseStart_7510445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510450 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_7510450 : Nat := 118140960795 + 7510450 * 2 ^ 59
def prefixEnd_7510450 : Nat := 4983230072969 + 3 ^ 40 * 7510450 * 2
def baseEnd_7510450 : Nat := 3856470781560245563535075

theorem tailTrace_7510450 : CollatzResearch.WordTrace tailWord_7510450 prefixEnd_7510450 3856470781560245563535075 := by
  unfold tailWord_7510450
  simp only [CollatzResearch.WordTrace]
  refine ⟨68482153910232451896380201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182619077093953205057013869 68482153910232451896380201)
  ·
    refine ⟨51361615432674338922285151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68482153910232451896380201 51361615432674338922285151)
    ·
      refine ⟨77042423149011508383427727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51361615432674338922285151 77042423149011508383427727)
      ·
        refine ⟨115563634723517262575141591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77042423149011508383427727 115563634723517262575141591)
        ·
          refine ⟨173345452085275893862712387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115563634723517262575141591 173345452085275893862712387)
          ·
            refine ⟨260018178127913840794068581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173345452085275893862712387 260018178127913840794068581)
            ·
              refine ⟨48753408398983845148887859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260018178127913840794068581 48753408398983845148887859)
              ·
                refine ⟨73130112598475767723331789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48753408398983845148887859 73130112598475767723331789)
                ·
                  refine ⟨27423792224428412896249421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73130112598475767723331789 27423792224428412896249421)
                  ·
                    refine ⟨10283922084160654836093533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27423792224428412896249421 10283922084160654836093533)
                    ·
                      refine ⟨3856470781560245563535075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10283922084160654836093533 3856470781560245563535075)
                      ·
                        rfl

theorem cell23_7510450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_7510450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510450 prefixEnd_7510450 := by exact prefixLift 7510450
  have htrace : WordTrace (prefixWord ++ tailWord_7510450) baseStart_7510450 baseEnd_7510450 := by
    simpa [prefixWord, tailWord_7510450, baseEnd_7510450] using wordTrace_append hprefix tailTrace_7510450
  have hstable : (prefixWord ++ tailWord_7510450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510450).length < 2 ^ (prefixWord ++ tailWord_7510450).sum := by decide
  have hdescent : baseEnd_7510450 < baseStart_7510450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510467 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 3]
def baseStart_7510467 : Nat := 118140960795 + 7510467 * 2 ^ 59
def prefixEnd_7510467 : Nat := 4983230072969 + 3 ^ 40 * 7510467 * 2
def baseEnd_7510467 : Nat := 3856479510731371997022497

theorem tailTrace_7510467 : CollatzResearch.WordTrace tailWord_7510467 prefixEnd_7510467 3856479510731371997022497 := by
  unfold tailWord_7510467
  simp only [CollatzResearch.WordTrace]
  refine ⟨273929235681868219488889655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182619490454578812992593103 273929235681868219488889655)
  ·
    refine ⟨410893853522802329233334483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273929235681868219488889655 410893853522802329233334483)
    ·
      refine ⟨616340780284203493850001725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410893853522802329233334483 616340780284203493850001725)
      ·
        refine ⟨231127792606576310193750647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 616340780284203493850001725 231127792606576310193750647)
        ·
          refine ⟨346691688909864465290625971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231127792606576310193750647 346691688909864465290625971)
          ·
            refine ⟨520037533364796697935938957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346691688909864465290625971 520037533364796697935938957)
            ·
              refine ⟨195014075011798761725977109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520037533364796697935938957 195014075011798761725977109)
              ·
                refine ⟨9141284766178066955905177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195014075011798761725977109 9141284766178066955905177)
                ·
                  refine ⟨6855963574633550216928883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9141284766178066955905177 6855963574633550216928883)
                  ·
                    refine ⟨10283945361950325325393325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6855963574633550216928883 10283945361950325325393325)
                    ·
                      refine ⟨3856479510731371997022497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10283945361950325325393325 3856479510731371997022497)
                      ·
                        rfl

theorem cell23_7510467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_7510467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510467 prefixEnd_7510467 := by exact prefixLift 7510467
  have htrace : WordTrace (prefixWord ++ tailWord_7510467) baseStart_7510467 baseEnd_7510467 := by
    simpa [prefixWord, tailWord_7510467, baseEnd_7510467] using wordTrace_append hprefix tailTrace_7510467
  have hstable : (prefixWord ++ tailWord_7510467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510467).length < 2 ^ (prefixWord ++ tailWord_7510467).sum := by decide
  have hdescent : baseEnd_7510467 < baseStart_7510467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510468 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_7510468 : Nat := 118140960795 + 7510468 * 2 ^ 59
def prefixEnd_7510468 : Nat := 4983230072969 + 3 ^ 40 * 7510468 * 2
def baseEnd_7510468 : Nat := 3856480024212026493109993

theorem tailTrace_7510468 : CollatzResearch.WordTrace tailWord_7510468 prefixEnd_7510468 3856480024212026493109993 := by
  unfold tailWord_7510468
  simp only [CollatzResearch.WordTrace]
  refine ⟨136964636077432298329838029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182619514769909731106450705 136964636077432298329838029)
  ·
    refine ⟨51361738529037111873689261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136964636077432298329838029 51361738529037111873689261)
    ·
      refine ⟨19260651948388916952633473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51361738529037111873689261 19260651948388916952633473)
      ·
        refine ⟨14445488961291687714475105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19260651948388916952633473 14445488961291687714475105)
        ·
          refine ⟨10834116720968765785856329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14445488961291687714475105 10834116720968765785856329)
          ·
            refine ⟨8125587540726574339392247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10834116720968765785856329 8125587540726574339392247)
            ·
              refine ⟨12188381311089861509088371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125587540726574339392247 12188381311089861509088371)
              ·
                refine ⟨18282571966634792263632557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12188381311089861509088371 18282571966634792263632557)
                ·
                  refine ⟨6855964487488047098862209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18282571966634792263632557 6855964487488047098862209)
                  ·
                    refine ⟨5141973365616035324146657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6855964487488047098862209 5141973365616035324146657)
                    ·
                      refine ⟨3856480024212026493109993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5141973365616035324146657 3856480024212026493109993)
                      ·
                        rfl

theorem cell23_7510468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_7510468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510468 prefixEnd_7510468 := by exact prefixLift 7510468
  have htrace : WordTrace (prefixWord ++ tailWord_7510468) baseStart_7510468 baseEnd_7510468 := by
    simpa [prefixWord, tailWord_7510468, baseEnd_7510468] using wordTrace_append hprefix tailTrace_7510468
  have hstable : (prefixWord ++ tailWord_7510468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510468).length < 2 ^ (prefixWord ++ tailWord_7510468).sum := by decide
  have hdescent : baseEnd_7510468 < baseStart_7510468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510483 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 8, 6]
def baseStart_7510483 : Nat := 118140960795 + 7510483 * 2 ^ 59
def prefixEnd_7510483 : Nat := 4983230072969 + 3 ^ 40 * 7510483 * 2
def baseEnd_7510483 : Nat := 1285495908807281311474141

theorem tailTrace_7510483 : CollatzResearch.WordTrace tailWord_7510483 prefixEnd_7510483 1285495908807281311474141 := by
  unfold tailWord_7510483
  simp only [CollatzResearch.WordTrace]
  refine ⟨273929819249810254221472103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182619879499873502814314735 273929819249810254221472103)
  ·
    refine ⟨410894728874715381332208155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273929819249810254221472103 410894728874715381332208155)
    ·
      refine ⟨616342093312073071998312233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410894728874715381332208155 616342093312073071998312233)
      ·
        refine ⟨462256569984054803998734175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616342093312073071998312233 462256569984054803998734175)
        ·
          refine ⟨693384854976082205998101263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462256569984054803998734175 693384854976082205998101263)
          ·
            refine ⟨1040077282464123308997151895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693384854976082205998101263 1040077282464123308997151895)
            ·
              refine ⟨1560115923696184963495727843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040077282464123308997151895 1560115923696184963495727843)
              ·
                refine ⟨2340173885544277445243591765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560115923696184963495727843 2340173885544277445243591765)
                ·
                  refine ⟨27423912721222001311448341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2340173885544277445243591765 27423912721222001311448341)
                  ·
                    refine ⟨1285495908807281311474141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27423912721222001311448341 1285495908807281311474141)
                    ·
                      rfl

theorem cell23_7510483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 6].length) (baseStart_7510483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510483 prefixEnd_7510483 := by exact prefixLift 7510483
  have htrace : WordTrace (prefixWord ++ tailWord_7510483) baseStart_7510483 baseEnd_7510483 := by
    simpa [prefixWord, tailWord_7510483, baseEnd_7510483] using wordTrace_append hprefix tailTrace_7510483
  have hstable : (prefixWord ++ tailWord_7510483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510483).length < 2 ^ (prefixWord ++ tailWord_7510483).sum := by decide
  have hdescent : baseEnd_7510483 < baseStart_7510483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510507 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 1, 4, 2]
def baseStart_7510507 : Nat := 118140960795 + 7510507 * 2 ^ 59
def prefixEnd_7510507 : Nat := 4983230072969 + 3 ^ 40 * 7510507 * 2
def baseEnd_7510507 : Nat := 3856500049957551840522313

theorem tailTrace_7510507 : CollatzResearch.WordTrace tailWord_7510507 prefixEnd_7510507 3856500049957551840522313 := by
  unfold tailWord_7510507
  simp only [CollatzResearch.WordTrace]
  refine ⟨273930694601723306320345775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182620463067815537546897183 273930694601723306320345775)
  ·
    refine ⟨410896041902584959480518663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273930694601723306320345775 410896041902584959480518663)
    ·
      refine ⟨616344062853877439220777995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410896041902584959480518663 616344062853877439220777995)
      ·
        refine ⟨924516094280816158831166993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616344062853877439220777995 924516094280816158831166993)
        ·
          refine ⟨693387070710612119123375245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924516094280816158831166993 693387070710612119123375245)
          ·
            refine ⟨260020151516479544671265717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 693387070710612119123375245 260020151516479544671265717)
            ·
              refine ⟨24376889204669957312931161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260020151516479544671265717 24376889204669957312931161)
              ·
                refine ⟨18282666903502467984698371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24376889204669957312931161 18282666903502467984698371)
                ·
                  refine ⟨27424000355253701977047557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18282666903502467984698371 27424000355253701977047557)
                  ·
                    refine ⟨5142000066610069120696417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27424000355253701977047557 5142000066610069120696417)
                    ·
                      refine ⟨3856500049957551840522313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5142000066610069120696417 3856500049957551840522313)
                      ·
                        rfl

theorem cell23_7510507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 4, 2].length) (baseStart_7510507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510507 prefixEnd_7510507 := by exact prefixLift 7510507
  have htrace : WordTrace (prefixWord ++ tailWord_7510507) baseStart_7510507 baseEnd_7510507 := by
    simpa [prefixWord, tailWord_7510507, baseEnd_7510507] using wordTrace_append hprefix tailTrace_7510507
  have hstable : (prefixWord ++ tailWord_7510507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510507).length < 2 ^ (prefixWord ++ tailWord_7510507).sum := by decide
  have hdescent : baseEnd_7510507 < baseStart_7510507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510520 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_7510520 : Nat := 118140960795 + 7510520 * 2 ^ 59
def prefixEnd_7510520 : Nat := 4983230072969 + 3 ^ 40 * 7510520 * 2
def baseEnd_7510520 : Nat := 3856506725206060289659753

theorem tailTrace_7510520 : CollatzResearch.WordTrace tailWord_7510520 prefixEnd_7510520 3856506725206060289659753 := by
  unfold tailWord_7510520
  simp only [CollatzResearch.WordTrace]
  refine ⟨136965584375338104770284507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182620779167117473027046009 136965584375338104770284507)
  ·
    refine ⟨205448376563007157155426761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136965584375338104770284507 205448376563007157155426761)
    ·
      refine ⟨154086282422255367866570071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205448376563007157155426761 154086282422255367866570071)
      ·
        refine ⟨231129423633383051799855107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154086282422255367866570071 231129423633383051799855107)
        ·
          refine ⟨346694135450074577699782661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231129423633383051799855107 346694135450074577699782661)
          ·
            refine ⟨65005150396888983318709249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346694135450074577699782661 65005150396888983318709249)
            ·
              refine ⟨48753862797666737489031937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65005150396888983318709249 48753862797666737489031937)
              ·
                refine ⟨36565397098250053116773953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48753862797666737489031937 36565397098250053116773953)
                ·
                  refine ⟨27424047823687539837580465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36565397098250053116773953 27424047823687539837580465)
                  ·
                    refine ⟨20568035867765654878185349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27424047823687539837580465 20568035867765654878185349)
                    ·
                      refine ⟨3856506725206060289659753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20568035867765654878185349 3856506725206060289659753)
                      ·
                        rfl

theorem cell23_7510520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_7510520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510520 prefixEnd_7510520 := by exact prefixLift 7510520
  have htrace : WordTrace (prefixWord ++ tailWord_7510520) baseStart_7510520 baseEnd_7510520 := by
    simpa [prefixWord, tailWord_7510520, baseEnd_7510520] using wordTrace_append hprefix tailTrace_7510520
  have hstable : (prefixWord ++ tailWord_7510520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510520).length < 2 ^ (prefixWord ++ tailWord_7510520).sum := by decide
  have hdescent : baseEnd_7510520 < baseStart_7510520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510607 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 3, 4]
def baseStart_7510607 : Nat := 118140960795 + 7510607 * 2 ^ 59
def prefixEnd_7510607 : Nat := 4983230072969 + 3 ^ 40 * 7510607 * 2
def baseEnd_7510607 : Nat := 1285517132674333816423951

theorem tailTrace_7510607 : CollatzResearch.WordTrace tailWord_7510607 prefixEnd_7510607 1285517132674333816423951 := by
  unfold tailWord_7510607
  simp only [CollatzResearch.WordTrace]
  refine ⟨273934341901361023398986075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182622894600907348932657383 273934341901361023398986075)
  ·
    refine ⟨410901512852041535098479113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273934341901361023398986075 410901512852041535098479113)
    ·
      refine ⟨308176134639031151323859335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410901512852041535098479113 308176134639031151323859335)
      ·
        refine ⟨462264201958546726985789003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308176134639031151323859335 462264201958546726985789003)
        ·
          refine ⟨693396302937820090478683505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462264201958546726985789003 693396302937820090478683505)
          ·
            refine ⟨520047227203365067859012629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693396302937820090478683505 520047227203365067859012629)
            ·
              refine ⟨24377213775157737555891217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 520047227203365067859012629 24377213775157737555891217)
              ·
                refine ⟨18282910331368303166918413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24377213775157737555891217 18282910331368303166918413)
                ·
                  refine ⟨6856091374263113687594405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18282910331368303166918413 6856091374263113687594405)
                  ·
                    refine ⟨1285517132674333816423951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6856091374263113687594405 1285517132674333816423951)
                    ·
                      rfl

theorem cell23_7510607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 4].length) (baseStart_7510607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510607 prefixEnd_7510607 := by exact prefixLift 7510607
  have htrace : WordTrace (prefixWord ++ tailWord_7510607) baseStart_7510607 baseEnd_7510607 := by
    simpa [prefixWord, tailWord_7510607, baseEnd_7510607] using wordTrace_append hprefix tailTrace_7510607
  have hstable : (prefixWord ++ tailWord_7510607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510607).length < 2 ^ (prefixWord ++ tailWord_7510607).sum := by decide
  have hdescent : baseEnd_7510607 < baseStart_7510607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510634 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_7510634 : Nat := 118140960795 + 7510634 * 2 ^ 59
def prefixEnd_7510634 : Nat := 4983230072969 + 3 ^ 40 * 7510634 * 2
def baseEnd_7510634 : Nat := 3856565262000672843634229

theorem tailTrace_7510634 : CollatzResearch.WordTrace tailWord_7510634 prefixEnd_7510634 3856565262000672843634229 := by
  unfold tailWord_7510634
  simp only [CollatzResearch.WordTrace]
  refine ⟨68483831668065801752554739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182623551114842138006812637 68483831668065801752554739)
  ·
    refine ⟨102725747502098702628832109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68483831668065801752554739 102725747502098702628832109)
    ·
      refine ⟨38522155313287013485812041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102725747502098702628832109 38522155313287013485812041)
      ·
        refine ⟨28891616484965260114359031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38522155313287013485812041 28891616484965260114359031)
        ·
          refine ⟨43337424727447890171538547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28891616484965260114359031 43337424727447890171538547)
          ·
            refine ⟨65006137091171835257307821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43337424727447890171538547 65006137091171835257307821)
            ·
              refine ⟨24377301409189438221490433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65006137091171835257307821 24377301409189438221490433)
              ·
                refine ⟨18282976056892078666117825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24377301409189438221490433 18282976056892078666117825)
                ·
                  refine ⟨13712232042669058999588369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18282976056892078666117825 13712232042669058999588369)
                  ·
                    refine ⟨10284174032001794249691277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13712232042669058999588369 10284174032001794249691277)
                    ·
                      refine ⟨3856565262000672843634229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10284174032001794249691277 3856565262000672843634229)
                      ·
                        rfl

theorem cell23_7510634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_7510634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510634 prefixEnd_7510634 := by exact prefixLift 7510634
  have htrace : WordTrace (prefixWord ++ tailWord_7510634) baseStart_7510634 baseEnd_7510634 := by
    simpa [prefixWord, tailWord_7510634, baseEnd_7510634] using wordTrace_append hprefix tailTrace_7510634
  have hstable : (prefixWord ++ tailWord_7510634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510634).length < 2 ^ (prefixWord ++ tailWord_7510634).sum := by decide
  have hdescent : baseEnd_7510634 < baseStart_7510634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510637 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 8]
def baseStart_7510637 : Nat := 118140960795 + 7510637 * 2 ^ 59
def prefixEnd_7510637 : Nat := 4983230072969 + 3 ^ 40 * 7510637 * 2
def baseEnd_7510637 : Nat := 428507422493626259099635

theorem tailTrace_7510637 : CollatzResearch.WordTrace tailWord_7510637 prefixEnd_7510637 428507422493626259099635 := by
  unfold tailWord_7510637
  simp only [CollatzResearch.WordTrace]
  refine ⟨273935436091252338522578165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182623624060834892348385443 273935436091252338522578165)
  ·
    refine ⟨25681447133554906736491703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 273935436091252338522578165 25681447133554906736491703)
    ·
      refine ⟨38522170700332360104737555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25681447133554906736491703 38522170700332360104737555)
      ·
        refine ⟨57783256050498540157106333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38522170700332360104737555 57783256050498540157106333)
        ·
          refine ⟨21668721018936952558914875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57783256050498540157106333 21668721018936952558914875)
          ·
            refine ⟨32503081528405428838372313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21668721018936952558914875 32503081528405428838372313)
            ·
              refine ⟨24377311146304071628779235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32503081528405428838372313 24377311146304071628779235)
              ·
                refine ⟨36565966719456107443168853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24377311146304071628779235 36565966719456107443168853)
                ·
                  refine ⟨428507422493626259099635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36565966719456107443168853 428507422493626259099635)
                  ·
                    rfl

theorem cell23_7510637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_7510637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510637 prefixEnd_7510637 := by exact prefixLift 7510637
  have htrace : WordTrace (prefixWord ++ tailWord_7510637) baseStart_7510637 baseEnd_7510637 := by
    simpa [prefixWord, tailWord_7510637, baseEnd_7510637] using wordTrace_append hprefix tailTrace_7510637
  have hstable : (prefixWord ++ tailWord_7510637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510637).length < 2 ^ (prefixWord ++ tailWord_7510637).sum := by decide
  have hdescent : baseEnd_7510637 < baseStart_7510637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510667 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 1, 5]
def baseStart_7510667 : Nat := 118140960795 + 7510667 * 2 ^ 59
def prefixEnd_7510667 : Nat := 4983230072969 + 3 ^ 40 * 7510667 * 2
def baseEnd_7510667 : Nat := 1285527402287423738173859

theorem tailTrace_7510667 : CollatzResearch.WordTrace tailWord_7510667 prefixEnd_7510667 1285527402287423738173859 := by
  unfold tailWord_7510667
  simp only [CollatzResearch.WordTrace]
  refine ⟨273936530281143653646170255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182624353520762435764113503 273936530281143653646170255)
  ·
    refine ⟨410904795421715480469255383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273936530281143653646170255 410904795421715480469255383)
    ·
      refine ⟨616357193132573220703883075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410904795421715480469255383 616357193132573220703883075)
      ·
        refine ⟨924535789698859831055824613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616357193132573220703883075 924535789698859831055824613)
        ·
          refine ⟨173350460568536218322967115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 924535789698859831055824613 173350460568536218322967115)
          ·
            refine ⟨260025690852804327484450673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173350460568536218322967115 260025690852804327484450673)
            ·
              refine ⟨195019268139603245613338005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260025690852804327484450673 195019268139603245613338005)
              ·
                refine ⟨9141528194043902138125219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195019268139603245613338005 9141528194043902138125219)
                ·
                  refine ⟨13712292291065853207187829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9141528194043902138125219 13712292291065853207187829)
                  ·
                    refine ⟨1285527402287423738173859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13712292291065853207187829 1285527402287423738173859)
                    ·
                      rfl

theorem cell23_7510667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 5].length) (baseStart_7510667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510667 prefixEnd_7510667 := by exact prefixLift 7510667
  have htrace : WordTrace (prefixWord ++ tailWord_7510667) baseStart_7510667 baseEnd_7510667 := by
    simpa [prefixWord, tailWord_7510667, baseEnd_7510667] using wordTrace_append hprefix tailTrace_7510667
  have hstable : (prefixWord ++ tailWord_7510667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510667).length < 2 ^ (prefixWord ++ tailWord_7510667).sum := by decide
  have hdescent : baseEnd_7510667 < baseStart_7510667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510681 : List Nat := [1, 2, 1, 2, 1, 2, 4, 5, 1, 1, 3]
def baseStart_7510681 : Nat := 118140960795 + 7510681 * 2 ^ 59
def prefixEnd_7510681 : Nat := 4983230072969 + 3 ^ 40 * 7510681 * 2
def baseEnd_7510681 : Nat := 3856589395591434159746513

theorem tailTrace_7510681 : CollatzResearch.WordTrace tailWord_7510681 prefixEnd_7510681 3856589395591434159746513 := by
  unfold tailWord_7510681
  simp only [CollatzResearch.WordTrace]
  refine ⟨273937040903092934037179897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182624693935395289358119931 273937040903092934037179897)
  ·
    refine ⟨205452780677319700527884923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273937040903092934037179897 205452780677319700527884923)
    ·
      refine ⟨308179171015979550791827385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205452780677319700527884923 308179171015979550791827385)
      ·
        refine ⟨231134378261984663093870539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308179171015979550791827385 231134378261984663093870539)
        ·
          refine ⟨346701567392976994640805809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231134378261984663093870539 346701567392976994640805809)
          ·
            refine ⟨260026175544732745980604357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346701567392976994640805809 260026175544732745980604357)
            ·
              refine ⟨48754907914637389871363317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260026175544732745980604357 48754907914637389871363317)
              ·
                refine ⟨4570772616997255300440311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48754907914637389871363317 4570772616997255300440311)
                ·
                  refine ⟨6856158925495882950660467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570772616997255300440311 6856158925495882950660467)
                  ·
                    refine ⟨10284238388243824425990701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6856158925495882950660467 10284238388243824425990701)
                    ·
                      refine ⟨3856589395591434159746513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10284238388243824425990701 3856589395591434159746513)
                      ·
                        rfl

theorem cell23_7510681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 1, 1, 3].length) (baseStart_7510681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510681 prefixEnd_7510681 := by exact prefixLift 7510681
  have htrace : WordTrace (prefixWord ++ tailWord_7510681) baseStart_7510681 baseEnd_7510681 := by
    simpa [prefixWord, tailWord_7510681, baseEnd_7510681] using wordTrace_append hprefix tailTrace_7510681
  have hstable : (prefixWord ++ tailWord_7510681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510681).length < 2 ^ (prefixWord ++ tailWord_7510681).sum := by decide
  have hdescent : baseEnd_7510681 < baseStart_7510681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510714 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_7510714 : Nat := 118140960795 + 7510714 * 2 ^ 59
def prefixEnd_7510714 : Nat := 4983230072969 + 3 ^ 40 * 7510714 * 2
def baseEnd_7510714 : Nat := 1285535446817677510211287

theorem tailTrace_7510714 : CollatzResearch.WordTrace tailWord_7510714 prefixEnd_7510714 1285535446817677510211287 := by
  unfold tailWord_7510714
  simp only [CollatzResearch.WordTrace]
  refine ⟨68484561127993345168282799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182625496341315587115420797 68484561127993345168282799)
  ·
    refine ⟨102726841691990017752424199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68484561127993345168282799 102726841691990017752424199)
    ·
      refine ⟨154090262537985026628636299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102726841691990017752424199 154090262537985026628636299)
      ·
        refine ⟨231135393806977539942954449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154090262537985026628636299 231135393806977539942954449)
        ·
          refine ⟨173351545355233154957215837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231135393806977539942954449 173351545355233154957215837)
          ·
            refine ⟨65006829508212433108955939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173351545355233154957215837 65006829508212433108955939)
            ·
              refine ⟨97510244262318649663433909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65006829508212433108955939 97510244262318649663433909)
              ·
                refine ⟨9141585399592373405946929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97510244262318649663433909 9141585399592373405946929)
                ·
                  refine ⟨6856189049694280054460197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9141585399592373405946929 6856189049694280054460197)
                  ·
                    refine ⟨1285535446817677510211287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6856189049694280054460197 1285535446817677510211287)
                    ·
                      rfl

theorem cell23_7510714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_7510714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510714 prefixEnd_7510714 := by exact prefixLift 7510714
  have htrace : WordTrace (prefixWord ++ tailWord_7510714) baseStart_7510714 baseEnd_7510714 := by
    simpa [prefixWord, tailWord_7510714, baseEnd_7510714] using wordTrace_append hprefix tailTrace_7510714
  have hstable : (prefixWord ++ tailWord_7510714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510714).length < 2 ^ (prefixWord ++ tailWord_7510714).sum := by decide
  have hdescent : baseEnd_7510714 < baseStart_7510714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510734 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_7510734 : Nat := 118140960795 + 7510734 * 2 ^ 59
def prefixEnd_7510734 : Nat := 4983230072969 + 3 ^ 40 * 7510734 * 2
def baseEnd_7510734 : Nat := 3856616610066122452383769

theorem tailTrace_7510734 : CollatzResearch.WordTrace tailWord_7510734 prefixEnd_7510734 3856616610066122452383769 := by
  unfold tailWord_7510734
  simp only [CollatzResearch.WordTrace]
  refine ⟨34242371746487615511107407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182625982647933949392572837 34242371746487615511107407)
  ·
    refine ⟨51363557619731423266661111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34242371746487615511107407 51363557619731423266661111)
    ·
      refine ⟨77045336429597134899991667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51363557619731423266661111 77045336429597134899991667)
      ·
        refine ⟨115568004644395702349987501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77045336429597134899991667 115568004644395702349987501)
        ·
          refine ⟨43338001741648388381245313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115568004644395702349987501 43338001741648388381245313)
          ·
            refine ⟨32503501306236291285933985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43338001741648388381245313 32503501306236291285933985)
            ·
              refine ⟨24377625979677218464450489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32503501306236291285933985 24377625979677218464450489)
              ·
                refine ⟨18283219484757913848337867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24377625979677218464450489 18283219484757913848337867)
                ·
                  refine ⟨27424829227136870772506801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18283219484757913848337867 27424829227136870772506801)
                  ·
                    refine ⟨20568621920352653079380101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27424829227136870772506801 20568621920352653079380101)
                    ·
                      refine ⟨3856616610066122452383769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20568621920352653079380101 3856616610066122452383769)
                      ·
                        rfl

theorem cell23_7510734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_7510734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510734 prefixEnd_7510734 := by exact prefixLift 7510734
  have htrace : WordTrace (prefixWord ++ tailWord_7510734) baseStart_7510734 baseEnd_7510734 := by
    simpa [prefixWord, tailWord_7510734, baseEnd_7510734] using wordTrace_append hprefix tailTrace_7510734
  have hstable : (prefixWord ++ tailWord_7510734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510734).length < 2 ^ (prefixWord ++ tailWord_7510734).sum := by decide
  have hdescent : baseEnd_7510734 < baseStart_7510734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510748 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_7510748 : Nat := 118140960795 + 7510748 * 2 ^ 59
def prefixEnd_7510748 : Nat := 4983230072969 + 3 ^ 40 * 7510748 * 2
def baseEnd_7510748 : Nat := 1285541266265095132536235

theorem tailTrace_7510748 : CollatzResearch.WordTrace tailWord_7510748 prefixEnd_7510748 1285541266265095132536235 := by
  unfold tailWord_7510748
  simp only [CollatzResearch.WordTrace]
  refine ⟨136969742296925102239934449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182626323062566802986579265 136969742296925102239934449)
  ·
    refine ⟨102727306722693826679950837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136969742296925102239934449 102727306722693826679950837)
    ·
      refine ⟨9630685005252546251245391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102727306722693826679950837 9630685005252546251245391)
      ·
        refine ⟨14446027507878819376868087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9630685005252546251245391 14446027507878819376868087)
        ·
          refine ⟨21669041261818229065302131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14446027507878819376868087 21669041261818229065302131)
          ·
            refine ⟨32503561892727343597953197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21669041261818229065302131 32503561892727343597953197)
            ·
              refine ⟨12188835709772753849232449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32503561892727343597953197 12188835709772753849232449)
              ·
                refine ⟨9141626782329565386924337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12188835709772753849232449 9141626782329565386924337)
                ·
                  refine ⟨6856220086747174040193253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9141626782329565386924337 6856220086747174040193253)
                  ·
                    refine ⟨1285541266265095132536235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6856220086747174040193253 1285541266265095132536235)
                    ·
                      rfl

theorem cell23_7510748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_7510748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510748 prefixEnd_7510748 := by exact prefixLift 7510748
  have htrace : WordTrace (prefixWord ++ tailWord_7510748) baseStart_7510748 baseEnd_7510748 := by
    simpa [prefixWord, tailWord_7510748, baseEnd_7510748] using wordTrace_append hprefix tailTrace_7510748
  have hstable : (prefixWord ++ tailWord_7510748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510748).length < 2 ^ (prefixWord ++ tailWord_7510748).sum := by decide
  have hdescent : baseEnd_7510748 < baseStart_7510748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510755 : List Nat := [1, 1, 1, 7, 1, 1, 2, 4, 1, 2, 2]
def baseStart_7510755 : Nat := 118140960795 + 7510755 * 2 ^ 59
def prefixEnd_7510755 : Nat := 4983230072969 + 3 ^ 40 * 7510755 * 2
def baseEnd_7510755 : Nat := 3856627393159866870221173

theorem tailTrace_7510755 : CollatzResearch.WordTrace tailWord_7510755 prefixEnd_7510755 3856627393159866870221173 := by
  unfold tailWord_7510755
  simp only [CollatzResearch.WordTrace]
  refine ⟨273939739904824844675373719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182626493269883229783582479 273939739904824844675373719)
  ·
    refine ⟨410909609857237267013060579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273939739904824844675373719 410909609857237267013060579)
    ·
      refine ⟨616364414785855900519590869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410909609857237267013060579 616364414785855900519590869)
      ·
        refine ⟨14446040971543497668427911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 616364414785855900519590869 14446040971543497668427911)
        ·
          refine ⟨21669061457315246502641867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14446040971543497668427911 21669061457315246502641867)
          ·
            refine ⟨32503592185972869753962801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21669061457315246502641867 32503592185972869753962801)
            ·
              refine ⟨24377694139479652315472101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32503592185972869753962801 24377694139479652315472101)
              ·
                refine ⟨4570817651152434809151019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24377694139479652315472101 4570817651152434809151019)
                ·
                  refine ⟨6856226476728652213726529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570817651152434809151019 6856226476728652213726529)
                  ·
                    refine ⟨5142169857546489160294897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6856226476728652213726529 5142169857546489160294897)
                    ·
                      refine ⟨3856627393159866870221173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5142169857546489160294897 3856627393159866870221173)
                      ·
                        rfl

theorem cell23_7510755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_7510755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510755 prefixEnd_7510755 := by exact prefixLift 7510755
  have htrace : WordTrace (prefixWord ++ tailWord_7510755) baseStart_7510755 baseEnd_7510755 := by
    simpa [prefixWord, tailWord_7510755, baseEnd_7510755] using wordTrace_append hprefix tailTrace_7510755
  have hstable : (prefixWord ++ tailWord_7510755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510755).length < 2 ^ (prefixWord ++ tailWord_7510755).sum := by decide
  have hdescent : baseEnd_7510755 < baseStart_7510755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510777 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_7510777 : Nat := 118140960795 + 7510777 * 2 ^ 59
def prefixEnd_7510777 : Nat := 4983230072969 + 3 ^ 40 * 7510777 * 2
def baseEnd_7510777 : Nat := 3856638689734265784146071

theorem tailTrace_7510777 : CollatzResearch.WordTrace tailWord_7510777 prefixEnd_7510777 3856638689734265784146071 := by
  unfold tailWord_7510777
  simp only [CollatzResearch.WordTrace]
  refine ⟨273940542310745142432674585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182627028207163428288449723 273940542310745142432674585)
  ·
    refine ⟨205455406733058856824505939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273940542310745142432674585 205455406733058856824505939)
    ·
      refine ⟨308183110099588285236758909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205455406733058856824505939 308183110099588285236758909)
      ·
        refine ⟨115568666287345606963784591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308183110099588285236758909 115568666287345606963784591)
        ·
          refine ⟨173352999431018410445676887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115568666287345606963784591 173352999431018410445676887)
          ·
            refine ⟨260029499146527615668515331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173352999431018410445676887 260029499146527615668515331)
            ·
              refine ⟨390044248719791423502772997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260029499146527615668515331 390044248719791423502772997)
              ·
                refine ⟨73133296634960891906769937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390044248719791423502772997 73133296634960891906769937)
                ·
                  refine ⟨54849972476220668930077453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73133296634960891906769937 54849972476220668930077453)
                  ·
                    refine ⟨20568739678582750848779045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54849972476220668930077453 20568739678582750848779045)
                    ·
                      refine ⟨3856638689734265784146071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20568739678582750848779045 3856638689734265784146071)
                      ·
                        rfl

theorem cell23_7510777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_7510777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510777 prefixEnd_7510777 := by exact prefixLift 7510777
  have htrace : WordTrace (prefixWord ++ tailWord_7510777) baseStart_7510777 baseEnd_7510777 := by
    simpa [prefixWord, tailWord_7510777, baseEnd_7510777] using wordTrace_append hprefix tailTrace_7510777
  have hstable : (prefixWord ++ tailWord_7510777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510777).length < 2 ^ (prefixWord ++ tailWord_7510777).sum := by decide
  have hdescent : baseEnd_7510777 < baseStart_7510777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510824 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_7510824 : Nat := 118140960795 + 7510824 * 2 ^ 59
def prefixEnd_7510824 : Nat := 4983230072969 + 3 ^ 40 * 7510824 * 2
def baseEnd_7510824 : Nat := 3856662823325027100258355

theorem tailTrace_7510824 : CollatzResearch.WordTrace tailWord_7510824 prefixEnd_7510824 3856662823325027100258355 := by
  unfold tailWord_7510824
  simp only [CollatzResearch.WordTrace]
  refine ⟨136971128270787434729817763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182628171027716579639757017 136971128270787434729817763)
  ·
    refine ⟨205456692406181152094726645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136971128270787434729817763 205456692406181152094726645)
    ·
      refine ⟨19261564913079483008880623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205456692406181152094726645 19261564913079483008880623)
      ·
        refine ⟨28892347369619224513320935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19261564913079483008880623 28892347369619224513320935)
        ·
          refine ⟨43338521054428836769981403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28892347369619224513320935 43338521054428836769981403)
          ·
            refine ⟨65007781581643255154972105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43338521054428836769981403 65007781581643255154972105)
            ·
              refine ⟨48755836186232441366229079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65007781581643255154972105 48755836186232441366229079)
              ·
                refine ⟨73133754279348662049343619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48755836186232441366229079 73133754279348662049343619)
                ·
                  refine ⟨109700631419022993074015429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73133754279348662049343619 109700631419022993074015429)
                  ·
                    refine ⟨20568868391066811201377893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109700631419022993074015429 20568868391066811201377893)
                    ·
                      refine ⟨3856662823325027100258355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20568868391066811201377893 3856662823325027100258355)
                      ·
                        rfl

theorem cell23_7510824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_7510824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510824 prefixEnd_7510824 := by exact prefixLift 7510824
  have htrace : WordTrace (prefixWord ++ tailWord_7510824) baseStart_7510824 baseEnd_7510824 := by
    simpa [prefixWord, tailWord_7510824, baseEnd_7510824] using wordTrace_append hprefix tailTrace_7510824
  have hstable : (prefixWord ++ tailWord_7510824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510824).length < 2 ^ (prefixWord ++ tailWord_7510824).sum := by decide
  have hdescent : baseEnd_7510824 < baseStart_7510824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510828 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 2, 2, 2]
def baseStart_7510828 : Nat := 118140960795 + 7510828 * 2 ^ 59
def prefixEnd_7510828 : Nat := 4983230072969 + 3 ^ 40 * 7510828 * 2
def baseEnd_7510828 : Nat := 3856664877247645084608337

theorem tailTrace_7510828 : CollatzResearch.WordTrace tailWord_7510828 prefixEnd_7510828 3856664877247645084608337 := by
  unfold tailWord_7510828
  simp only [CollatzResearch.WordTrace]
  refine ⟨136971201216780189071390569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182628268289040252095187425 136971201216780189071390569)
  ·
    refine ⟨102728400912585141803542927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136971201216780189071390569 102728400912585141803542927)
    ·
      refine ⟨154092601368877712705314391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102728400912585141803542927 154092601368877712705314391)
      ·
        refine ⟨231138902053316569057971587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154092601368877712705314391 231138902053316569057971587)
        ·
          refine ⟨346708353079974853586957381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231138902053316569057971587 346708353079974853586957381)
          ·
            refine ⟨65007816202495285047554509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346708353079974853586957381 65007816202495285047554509)
            ·
              refine ⟨24377931075935731892832941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65007816202495285047554509 24377931075935731892832941)
              ·
                refine ⟨9141724153475899459812353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24377931075935731892832941 9141724153475899459812353)
                ·
                  refine ⟨6856293115106924594859265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9141724153475899459812353 6856293115106924594859265)
                  ·
                    refine ⟨5142219836330193446144449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6856293115106924594859265 5142219836330193446144449)
                    ·
                      refine ⟨3856664877247645084608337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5142219836330193446144449 3856664877247645084608337)
                      ·
                        rfl

theorem cell23_7510828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_7510828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510828 prefixEnd_7510828 := by exact prefixLift 7510828
  have htrace : WordTrace (prefixWord ++ tailWord_7510828) baseStart_7510828 baseEnd_7510828 := by
    simpa [prefixWord, tailWord_7510828, baseEnd_7510828] using wordTrace_append hprefix tailTrace_7510828
  have hstable : (prefixWord ++ tailWord_7510828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510828).length < 2 ^ (prefixWord ++ tailWord_7510828).sum := by decide
  have hdescent : baseEnd_7510828 < baseStart_7510828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510844 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_7510844 : Nat := 118140960795 + 7510844 * 2 ^ 59
def prefixEnd_7510844 : Nat := 4983230072969 + 3 ^ 40 * 7510844 * 2
def baseEnd_7510844 : Nat := 3856673092938117022008263

theorem tailTrace_7510844 : CollatzResearch.WordTrace tailWord_7510844 prefixEnd_7510844 3856673092938117022008263 := by
  unfold tailWord_7510844
  simp only [CollatzResearch.WordTrace]
  refine ⟨136971493000751206437681793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182628657334334941916909057 136971493000751206437681793)
  ·
    refine ⟨102728619750563404828261345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136971493000751206437681793 102728619750563404828261345)
    ·
      refine ⟨77046464812922553621196009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102728619750563404828261345 77046464812922553621196009)
      ·
        refine ⟨57784848609691915215897007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77046464812922553621196009 57784848609691915215897007)
        ·
          refine ⟨86677272914537872823845511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57784848609691915215897007 86677272914537872823845511)
          ·
            refine ⟨130015909371806809235768267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86677272914537872823845511 130015909371806809235768267)
            ·
              refine ⟨195023864057710213853652401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130015909371806809235768267 195023864057710213853652401)
              ·
                refine ⟨146267898043282660390239301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195023864057710213853652401 146267898043282660390239301)
                ·
                  refine ⟨27425230883115498823169869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146267898043282660390239301 27425230883115498823169869)
                  ·
                    refine ⟨10284461581168312058688701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27425230883115498823169869 10284461581168312058688701)
                    ·
                      refine ⟨3856673092938117022008263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10284461581168312058688701 3856673092938117022008263)
                      ·
                        rfl

theorem cell23_7510844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_7510844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510844 prefixEnd_7510844 := by exact prefixLift 7510844
  have htrace : WordTrace (prefixWord ++ tailWord_7510844) baseStart_7510844 baseEnd_7510844 := by
    simpa [prefixWord, tailWord_7510844, baseEnd_7510844] using wordTrace_append hprefix tailTrace_7510844
  have hstable : (prefixWord ++ tailWord_7510844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510844).length < 2 ^ (prefixWord ++ tailWord_7510844).sum := by decide
  have hdescent : baseEnd_7510844 < baseStart_7510844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510864 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 2, 5]
def baseStart_7510864 : Nat := 118140960795 + 7510864 * 2 ^ 59
def prefixEnd_7510864 : Nat := 4983230072969 + 3 ^ 40 * 7510864 * 2
def baseEnd_7510864 : Nat := 1285561120850402314586057

theorem tailTrace_7510864 : CollatzResearch.WordTrace tailWord_7510864 prefixEnd_7510864 1285561120850402314586057 := by
  unfold tailWord_7510864
  simp only [CollatzResearch.WordTrace]
  refine ⟨136971857730714978145545823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182629143640953304194061097 136971857730714978145545823)
  ·
    refine ⟨205457786596072467218318735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136971857730714978145545823 205457786596072467218318735)
    ·
      refine ⟨308186679894108700827478103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205457786596072467218318735 308186679894108700827478103)
      ·
        refine ⟨462280019841163051241217155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308186679894108700827478103 462280019841163051241217155)
        ·
          refine ⟨693420029761744576861825733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462280019841163051241217155 693420029761744576861825733)
          ·
            refine ⟨130016255580327108161592325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 693420029761744576861825733 130016255580327108161592325)
            ·
              refine ⟨24378047921311332780298561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130016255580327108161592325 24378047921311332780298561)
              ·
                refine ⟨18283535940983499585223921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24378047921311332780298561 18283535940983499585223921)
                ·
                  refine ⟨13712651955737624688917941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18283535940983499585223921 13712651955737624688917941)
                  ·
                    refine ⟨1285561120850402314586057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13712651955737624688917941 1285561120850402314586057)
                    ·
                      rfl

theorem cell23_7510864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_7510864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510864 prefixEnd_7510864 := by exact prefixLift 7510864
  have htrace : WordTrace (prefixWord ++ tailWord_7510864) baseStart_7510864 baseEnd_7510864 := by
    simpa [prefixWord, tailWord_7510864, baseEnd_7510864] using wordTrace_append hprefix tailTrace_7510864
  have hstable : (prefixWord ++ tailWord_7510864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510864).length < 2 ^ (prefixWord ++ tailWord_7510864).sum := by decide
  have hdescent : baseEnd_7510864 < baseStart_7510864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510868 : List Nat := [2, 4, 1, 1, 4, 1, 1, 4, 5]
def baseStart_7510868 : Nat := 118140960795 + 7510868 * 2 ^ 59
def prefixEnd_7510868 : Nat := 4983230072969 + 3 ^ 40 * 7510868 * 2
def baseEnd_7510868 : Nat := 428520601830424992012017

theorem tailTrace_7510868 : CollatzResearch.WordTrace tailWord_7510868 prefixEnd_7510868 428520601830424992012017 := by
  unfold tailWord_7510868
  simp only [CollatzResearch.WordTrace]
  refine ⟨136971930676707732487118629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182629240902276976649491505 136971930676707732487118629)
  ·
    refine ⟨25682237001882699841334743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136971930676707732487118629 25682237001882699841334743)
    ·
      refine ⟨38523355502824049762002115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25682237001882699841334743 38523355502824049762002115)
      ·
        refine ⟨57785033254236074643003173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38523355502824049762002115 57785033254236074643003173)
        ·
          refine ⟨10834693735169263995563095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57785033254236074643003173 10834693735169263995563095)
          ·
            refine ⟨16252040602753895993344643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10834693735169263995563095 16252040602753895993344643)
            ·
              refine ⟨24378060904130843990016965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16252040602753895993344643 24378060904130843990016965)
              ·
                refine ⟨4570886419524533248128181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24378060904130843990016965 4570886419524533248128181)
                ·
                  refine ⟨428520601830424992012017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4570886419524533248128181 428520601830424992012017)
                  ·
                    rfl

theorem cell23_7510868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_7510868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510868 prefixEnd_7510868 := by exact prefixLift 7510868
  have htrace : WordTrace (prefixWord ++ tailWord_7510868) baseStart_7510868 baseEnd_7510868 := by
    simpa [prefixWord, tailWord_7510868, baseEnd_7510868] using wordTrace_append hprefix tailTrace_7510868
  have hstable : (prefixWord ++ tailWord_7510868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510868).length < 2 ^ (prefixWord ++ tailWord_7510868).sum := by decide
  have hdescent : baseEnd_7510868 < baseStart_7510868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510871 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 2, 5, 2]
def baseStart_7510871 : Nat := 118140960795 + 7510871 * 2 ^ 59
def prefixEnd_7510871 : Nat := 4983230072969 + 3 ^ 40 * 7510871 * 2
def baseEnd_7510871 : Nat := 3856686956915788416370639

theorem tailTrace_7510871 : CollatzResearch.WordTrace tailWord_7510871 prefixEnd_7510871 3856686956915788416370639 := by
  unfold tailWord_7510871
  simp only [CollatzResearch.WordTrace]
  refine ⟨273943970772404596486596467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182629313848269730991064311 273943970772404596486596467)
  ·
    refine ⟨410915956158606894729894701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273943970772404596486596467 410915956158606894729894701)
    ·
      refine ⟨154093483559477585523710513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410915956158606894729894701 154093483559477585523710513)
      ·
        refine ⟨115570112669608189142782885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154093483559477585523710513 115570112669608189142782885)
        ·
          refine ⟨21669396125551535464271791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115570112669608189142782885 21669396125551535464271791)
          ·
            refine ⟨32504094188327303196407687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21669396125551535464271791 32504094188327303196407687)
            ·
              refine ⟨48756141282490954794611531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32504094188327303196407687 48756141282490954794611531)
              ·
                refine ⟨73134211923736432191917297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48756141282490954794611531 73134211923736432191917297)
                ·
                  refine ⟨54850658942802324143937973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73134211923736432191917297 54850658942802324143937973)
                  ·
                    refine ⟨5142249275887717888494185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54850658942802324143937973 5142249275887717888494185)
                    ·
                      refine ⟨3856686956915788416370639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5142249275887717888494185 3856686956915788416370639)
                      ·
                        rfl

theorem cell23_7510871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_7510871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510871 prefixEnd_7510871 := by exact prefixLift 7510871
  have htrace : WordTrace (prefixWord ++ tailWord_7510871) baseStart_7510871 baseEnd_7510871 := by
    simpa [prefixWord, tailWord_7510871, baseEnd_7510871] using wordTrace_append hprefix tailTrace_7510871
  have hstable : (prefixWord ++ tailWord_7510871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510871).length < 2 ^ (prefixWord ++ tailWord_7510871).sum := by decide
  have hdescent : baseEnd_7510871 < baseStart_7510871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510874 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5]
def baseStart_7510874 : Nat := 118140960795 + 7510874 * 2 ^ 59
def prefixEnd_7510874 : Nat := 4983230072969 + 3 ^ 40 * 7510874 * 2
def baseEnd_7510874 : Nat := 3856688497357751904633125

theorem tailTrace_7510874 : CollatzResearch.WordTrace tailWord_7510874 prefixEnd_7510874 3856688497357751904633125 := by
  unfold tailWord_7510874
  simp only [CollatzResearch.WordTrace]
  refine ⟨68486020047848431999738919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182629386794262485332637117 68486020047848431999738919)
  ·
    refine ⟨102729030071772647999608379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68486020047848431999738919 102729030071772647999608379)
    ·
      refine ⟨154093545107658971999412569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102729030071772647999608379 154093545107658971999412569)
      ·
        refine ⟨115570158830744228999559427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154093545107658971999412569 115570158830744228999559427)
        ·
          refine ⟨173355238246116343499339141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115570158830744228999559427 173355238246116343499339141)
          ·
            refine ⟨32504107171146814406126089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173355238246116343499339141 32504107171146814406126089)
            ·
              refine ⟨24378080378360110804594567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32504107171146814406126089 24378080378360110804594567)
              ·
                refine ⟨36567120567540166206891851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24378080378360110804594567 36567120567540166206891851)
                ·
                  refine ⟨54850680851310249310337777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36567120567540166206891851 54850680851310249310337777)
                  ·
                    refine ⟨41138010638482686982753333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54850680851310249310337777 41138010638482686982753333)
                    ·
                      refine ⟨3856688497357751904633125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41138010638482686982753333 3856688497357751904633125)
                      ·
                        rfl

theorem cell23_7510874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_7510874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510874 prefixEnd_7510874 := by exact prefixLift 7510874
  have htrace : WordTrace (prefixWord ++ tailWord_7510874) baseStart_7510874 baseEnd_7510874 := by
    simpa [prefixWord, tailWord_7510874, baseEnd_7510874] using wordTrace_append hprefix tailTrace_7510874
  have hstable : (prefixWord ++ tailWord_7510874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510874).length < 2 ^ (prefixWord ++ tailWord_7510874).sum := by decide
  have hdescent : baseEnd_7510874 < baseStart_7510874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510901 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7510901 : Nat := 118140960795 + 7510901 * 2 ^ 59
def prefixEnd_7510901 : Nat := 4983230072969 + 3 ^ 40 * 7510901 * 2
def baseEnd_7510901 : Nat := 3856702361335423298995501

theorem tailTrace_7510901 : CollatzResearch.WordTrace tailWord_7510901 prefixEnd_7510901 3856702361335423298995501 := by
  unfold tailWord_7510901
  simp only [CollatzResearch.WordTrace]
  refine ⟨273945064962295911610188557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182630043308197274406792371 273945064962295911610188557)
  ·
    refine ⟨102729399360860966853820709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273945064962295911610188557 102729399360860966853820709)
    ·
      refine ⟨19261762380161431285091383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102729399360860966853820709 19261762380161431285091383)
      ·
        refine ⟨28892643570242146927637075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19261762380161431285091383 28892643570242146927637075)
        ·
          refine ⟨43338965355363220391455613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28892643570242146927637075 43338965355363220391455613)
          ·
            refine ⟨16252112008261207646795855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43338965355363220391455613 16252112008261207646795855)
            ·
              refine ⟨24378168012391811470193783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16252112008261207646795855 24378168012391811470193783)
              ·
                refine ⟨36567252018587717205290675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24378168012391811470193783 36567252018587717205290675)
                ·
                  refine ⟨54850878027881575807936013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36567252018587717205290675 54850878027881575807936013)
                  ·
                    refine ⟨20569079260455590927976005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54850878027881575807936013 20569079260455590927976005)
                    ·
                      refine ⟨3856702361335423298995501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20569079260455590927976005 3856702361335423298995501)
                      ·
                        rfl

theorem cell23_7510901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7510901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7510901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7510901 prefixEnd_7510901 := by exact prefixLift 7510901
  have htrace : WordTrace (prefixWord ++ tailWord_7510901) baseStart_7510901 baseEnd_7510901 := by
    simpa [prefixWord, tailWord_7510901, baseEnd_7510901] using wordTrace_append hprefix tailTrace_7510901
  have hstable : (prefixWord ++ tailWord_7510901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510901).length < 2 ^ (prefixWord ++ tailWord_7510901).sum := by decide
  have hdescent : baseEnd_7510901 < baseStart_7510901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511005 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_7511005 : Nat := 118140960795 + 7511005 * 2 ^ 59
def prefixEnd_7511005 : Nat := 4983230072969 + 3 ^ 40 * 7511005 * 2
def baseEnd_7511005 : Nat := 1285585254441163630698341

theorem tailTrace_7511005 : CollatzResearch.WordTrace tailWord_7511005 prefixEnd_7511005 1285585254441163630698341 := by
  unfold tailWord_7511005
  simp only [CollatzResearch.WordTrace]
  refine ⟨273948858153919137371974469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182632572102612758247982979 273948858153919137371974469)
  ·
    refine ⟨51365410903859838257245213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273948858153919137371974469 51365410903859838257245213)
    ·
      refine ⟨19262029088947439346466955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51365410903859838257245213 19262029088947439346466955)
      ·
        refine ⟨28893043633421159019700433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19262029088947439346466955 28893043633421159019700433)
        ·
          refine ⟨21669782725065869264775325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28893043633421159019700433 21669782725065869264775325)
          ·
            refine ⟨8126168521899700974290747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21669782725065869264775325 8126168521899700974290747)
            ·
              refine ⟨12189252782849551461436121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126168521899700974290747 12189252782849551461436121)
              ·
                refine ⟨9141939587137163596077091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12189252782849551461436121 9141939587137163596077091)
                ·
                  refine ⟨13712909380705745394115637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9141939587137163596077091 13712909380705745394115637)
                  ·
                    refine ⟨1285585254441163630698341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13712909380705745394115637 1285585254441163630698341)
                    ·
                      rfl

theorem cell23_7511005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_7511005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511005 prefixEnd_7511005 := by exact prefixLift 7511005
  have htrace : WordTrace (prefixWord ++ tailWord_7511005) baseStart_7511005 baseEnd_7511005 := by
    simpa [prefixWord, tailWord_7511005, baseEnd_7511005] using wordTrace_append hprefix tailTrace_7511005
  have hstable : (prefixWord ++ tailWord_7511005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511005).length < 2 ^ (prefixWord ++ tailWord_7511005).sum := by decide
  have hdescent : baseEnd_7511005 < baseStart_7511005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511025 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 1, 1, 4]
def baseStart_7511025 : Nat := 118140960795 + 7511025 * 2 ^ 59
def prefixEnd_7511025 : Nat := 4983230072969 + 3 ^ 40 * 7511025 * 2
def baseEnd_7511025 : Nat := 3856766032936580813844931

theorem tailTrace_7511025 : CollatzResearch.WordTrace tailWord_7511025 prefixEnd_7511025 3856766032936580813844931 := by
  unfold tailWord_7511025
  simp only [CollatzResearch.WordTrace]
  refine ⟨273949587613846680787702529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182633058409231120525135019 273949587613846680787702529)
  ·
    refine ⟨205462190710385010590776897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273949587613846680787702529 205462190710385010590776897)
    ·
      refine ⟨154096643032788757943082673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205462190710385010590776897 154096643032788757943082673)
      ·
        refine ⟨115572482274591568457312005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154096643032788757943082673 115572482274591568457312005)
        ·
          refine ⟨21669840426485919085746001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115572482274591568457312005 21669840426485919085746001)
          ·
            refine ⟨16252380319864439314309501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21669840426485919085746001 16252380319864439314309501)
            ·
              refine ⟨6094642619949164742866063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16252380319864439314309501 6094642619949164742866063)
              ·
                refine ⟨9141963929923747114299095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094642619949164742866063 9141963929923747114299095)
                ·
                  refine ⟨13712945894885620671448643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9141963929923747114299095 13712945894885620671448643)
                  ·
                    refine ⟨20569418842328431007172965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13712945894885620671448643 20569418842328431007172965)
                    ·
                      refine ⟨3856766032936580813844931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20569418842328431007172965 3856766032936580813844931)
                      ·
                        rfl

theorem cell23_7511025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_7511025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511025 prefixEnd_7511025 := by exact prefixLift 7511025
  have htrace : WordTrace (prefixWord ++ tailWord_7511025) baseStart_7511025 baseEnd_7511025 := by
    simpa [prefixWord, tailWord_7511025, baseEnd_7511025] using wordTrace_append hprefix tailTrace_7511025
  have hstable : (prefixWord ++ tailWord_7511025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511025).length < 2 ^ (prefixWord ++ tailWord_7511025).sum := by decide
  have hdescent : baseEnd_7511025 < baseStart_7511025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511079 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_7511079 : Nat := 118140960795 + 7511079 * 2 ^ 59
def prefixEnd_7511079 : Nat := 4983230072969 + 3 ^ 40 * 7511079 * 2
def baseEnd_7511079 : Nat := 3856793760891923602569683

theorem tailTrace_7511079 : CollatzResearch.WordTrace tailWord_7511079 prefixEnd_7511079 3856793760891923602569683 := by
  unfold tailWord_7511079
  simp only [CollatzResearch.WordTrace]
  refine ⟨273951557155651048010168291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182634371437100698673445527 273951557155651048010168291)
  ·
    refine ⟨410927335733476572015252437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273951557155651048010168291 410927335733476572015252437)
    ·
      refine ⟨9631109431253357156607479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 410927335733476572015252437 9631109431253357156607479)
      ·
        refine ⟨14446664146880035734911219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9631109431253357156607479 14446664146880035734911219)
        ·
          refine ⟨21669996220320053602366829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14446664146880035734911219 21669996220320053602366829)
          ·
            refine ⟨8126248582620020100887561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21669996220320053602366829 8126248582620020100887561)
            ·
              refine ⟨6094686436965015075665671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8126248582620020100887561 6094686436965015075665671)
              ·
                refine ⟨9142029655447522613498507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094686436965015075665671 9142029655447522613498507)
                ·
                  refine ⟨13713044483171283920247761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9142029655447522613498507 13713044483171283920247761)
                  ·
                    refine ⟨10284783362378462940185821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13713044483171283920247761 10284783362378462940185821)
                    ·
                      refine ⟨3856793760891923602569683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10284783362378462940185821 3856793760891923602569683)
                      ·
                        rfl

theorem cell23_7511079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_7511079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511079 prefixEnd_7511079 := by exact prefixLift 7511079
  have htrace : WordTrace (prefixWord ++ tailWord_7511079) baseStart_7511079 baseEnd_7511079 := by
    simpa [prefixWord, tailWord_7511079, baseEnd_7511079] using wordTrace_append hprefix tailTrace_7511079
  have hstable : (prefixWord ++ tailWord_7511079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511079).length < 2 ^ (prefixWord ++ tailWord_7511079).sum := by decide
  have hdescent : baseEnd_7511079 < baseStart_7511079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511092 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_7511092 : Nat := 118140960795 + 7511092 * 2 ^ 59
def prefixEnd_7511092 : Nat := 4983230072969 + 3 ^ 40 * 7511092 * 2
def baseEnd_7511092 : Nat := 3856800436140432051707123

theorem tailTrace_7511092 : CollatzResearch.WordTrace tailWord_7511092 prefixEnd_7511092 3856800436140432051707123 := by
  unfold tailWord_7511092
  simp only [CollatzResearch.WordTrace]
  refine ⟨136976015652301975615195765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182634687536402634153594353 136976015652301975615195765)
  ·
    refine ⟨12841501467403310213924603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136976015652301975615195765 12841501467403310213924603)
    ·
      refine ⟨19262252201104965320886905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12841501467403310213924603 19262252201104965320886905)
      ·
        refine ⟨14446689150828723990665179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19262252201104965320886905 14446689150828723990665179)
        ·
          refine ⟨21670033726243085985997769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14446689150828723990665179 21670033726243085985997769)
          ·
            refine ⟨16252525294682314489498327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21670033726243085985997769 16252525294682314489498327)
            ·
              refine ⟨24378787942023471734247491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16252525294682314489498327 24378787942023471734247491)
              ·
                refine ⟨36568181913035207601371237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24378787942023471734247491 36568181913035207601371237)
                ·
                  refine ⟨6856534108694101425257107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36568181913035207601371237 6856534108694101425257107)
                  ·
                    refine ⟨10284801163041152137885661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6856534108694101425257107 10284801163041152137885661)
                    ·
                      refine ⟨3856800436140432051707123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10284801163041152137885661 3856800436140432051707123)
                      ·
                        rfl

theorem cell23_7511092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_7511092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511092 prefixEnd_7511092 := by exact prefixLift 7511092
  have htrace : WordTrace (prefixWord ++ tailWord_7511092) baseStart_7511092 baseEnd_7511092 := by
    simpa [prefixWord, tailWord_7511092, baseEnd_7511092] using wordTrace_append hprefix tailTrace_7511092
  have hstable : (prefixWord ++ tailWord_7511092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511092).length < 2 ^ (prefixWord ++ tailWord_7511092).sum := by decide
  have hdescent : baseEnd_7511092 < baseStart_7511092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511098 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2]
def baseStart_7511098 : Nat := 118140960795 + 7511098 * 2 ^ 59
def prefixEnd_7511098 : Nat := 4983230072969 + 3 ^ 40 * 7511098 * 2
def baseEnd_7511098 : Nat := 3856803517024359028232095

theorem tailTrace_7511098 : CollatzResearch.WordTrace tailWord_7511098 prefixEnd_7511098 3856803517024359028232095 := by
  unfold tailWord_7511098
  simp only [CollatzResearch.WordTrace]
  refine ⟨68488062535645553563777487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182634833428388142836739965 68488062535645553563777487)
  ·
    refine ⟨102732093803468330345666231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68488062535645553563777487 102732093803468330345666231)
    ·
      refine ⟨154098140705202495518499347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102732093803468330345666231 154098140705202495518499347)
      ·
        refine ⟨231147211057803743277749021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154098140705202495518499347 231147211057803743277749021)
        ·
          refine ⟨86680204146676403729155883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231147211057803743277749021 86680204146676403729155883)
          ·
            refine ⟨130020306220014605593733825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86680204146676403729155883 130020306220014605593733825)
            ·
              refine ⟨97515229665010954195300369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130020306220014605593733825 97515229665010954195300369)
              ·
                refine ⟨73136422248758215646475277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97515229665010954195300369 73136422248758215646475277)
                ·
                  refine ⟨27426158343284330867428229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73136422248758215646475277 27426158343284330867428229)
                  ·
                    refine ⟨5142404689365812037642793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27426158343284330867428229 5142404689365812037642793)
                    ·
                      refine ⟨3856803517024359028232095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5142404689365812037642793 3856803517024359028232095)
                      ·
                        rfl

theorem cell23_7511098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_7511098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511098 prefixEnd_7511098 := by exact prefixLift 7511098
  have htrace : WordTrace (prefixWord ++ tailWord_7511098) baseStart_7511098 baseEnd_7511098 := by
    simpa [prefixWord, tailWord_7511098, baseEnd_7511098] using wordTrace_append hprefix tailTrace_7511098
  have hstable : (prefixWord ++ tailWord_7511098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511098).length < 2 ^ (prefixWord ++ tailWord_7511098).sum := by decide
  have hdescent : baseEnd_7511098 < baseStart_7511098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511121 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 7]
def baseStart_7511121 : Nat := 118140960795 + 7511121 * 2 ^ 59
def prefixEnd_7511121 : Nat := 4983230072969 + 3 ^ 40 * 7511121 * 2
def baseEnd_7511121 : Nat := 428535036342156937582721

theorem tailTrace_7511121 : CollatzResearch.WordTrace tailWord_7511121 prefixEnd_7511121 428535036342156937582721 := by
  unfold tailWord_7511121
  simp only [CollatzResearch.WordTrace]
  refine ⟨273953089021498889183197217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182635392680999259455464811 273953089021498889183197217)
  ·
    refine ⟨205464816766124166887397913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273953089021498889183197217 205464816766124166887397913)
    ·
      refine ⟨154098612574593125165548435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205464816766124166887397913 154098612574593125165548435)
      ·
        refine ⟨231147918861889687748322653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154098612574593125165548435 231147918861889687748322653)
        ·
          refine ⟨86680469573208632905620995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231147918861889687748322653 86680469573208632905620995)
          ·
            refine ⟨130020704359812949358431493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86680469573208632905620995 130020704359812949358431493)
            ·
              refine ⟨24378882067464928004705905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130020704359812949358431493 24378882067464928004705905)
              ·
                refine ⟨18284161550598696003529429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24378882067464928004705905 18284161550598696003529429)
                ·
                  refine ⟨428535036342156937582721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18284161550598696003529429 428535036342156937582721)
                  ·
                    rfl

theorem cell23_7511121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 7].length) (baseStart_7511121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511121 prefixEnd_7511121 := by exact prefixLift 7511121
  have htrace : WordTrace (prefixWord ++ tailWord_7511121) baseStart_7511121 baseEnd_7511121 := by
    simpa [prefixWord, tailWord_7511121, baseEnd_7511121] using wordTrace_append hprefix tailTrace_7511121
  have hstable : (prefixWord ++ tailWord_7511121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511121).length < 2 ^ (prefixWord ++ tailWord_7511121).sum := by decide
  have hdescent : baseEnd_7511121 < baseStart_7511121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511242 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_7511242 : Nat := 118140960795 + 7511242 * 2 ^ 59
def prefixEnd_7511242 : Nat := 4983230072969 + 3 ^ 40 * 7511242 * 2
def baseEnd_7511242 : Nat := 3856877458238606464831433

theorem tailTrace_7511242 : CollatzResearch.WordTrace tailWord_7511242 prefixEnd_7511242 3856877458238606464831433 := by
  unfold tailWord_7511242
  simp only [CollatzResearch.WordTrace]
  refine ⟨68489375563515131712087995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182638334836040351232234653 68489375563515131712087995)
  ·
    refine ⟨102734063345272697568131993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68489375563515131712087995 102734063345272697568131993)
    ·
      refine ⟨77050547508954523176098995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102734063345272697568131993 77050547508954523176098995)
      ·
        refine ⟨115575821263431784764148493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77050547508954523176098995 115575821263431784764148493)
        ·
          refine ⟨43340932973786919286555685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115575821263431784764148493 43340932973786919286555685)
          ·
            refine ⟨8126424932585047366229191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43340932973786919286555685 8126424932585047366229191)
            ·
              refine ⟨12189637398877571049343787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126424932585047366229191 12189637398877571049343787)
              ·
                refine ⟨18284456098316356574015681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12189637398877571049343787 18284456098316356574015681)
                ·
                  refine ⟨13713342073737267430511761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18284456098316356574015681 13713342073737267430511761)
                  ·
                    refine ⟨10285006555302950572883821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13713342073737267430511761 10285006555302950572883821)
                    ·
                      refine ⟨3856877458238606464831433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285006555302950572883821 3856877458238606464831433)
                      ·
                        rfl

theorem cell23_7511242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_7511242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511242 prefixEnd_7511242 := by exact prefixLift 7511242
  have htrace : WordTrace (prefixWord ++ tailWord_7511242) baseStart_7511242 baseEnd_7511242 := by
    simpa [prefixWord, tailWord_7511242, baseEnd_7511242] using wordTrace_append hprefix tailTrace_7511242
  have hstable : (prefixWord ++ tailWord_7511242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511242).length < 2 ^ (prefixWord ++ tailWord_7511242).sum := by decide
  have hdescent : baseEnd_7511242 < baseStart_7511242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511251 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 7]
def baseStart_7511251 : Nat := 118140960795 + 7511251 * 2 ^ 59
def prefixEnd_7511251 : Nat := 4983230072969 + 3 ^ 40 * 7511251 * 2
def baseEnd_7511251 : Nat := 3856882079564496929618891

theorem tailTrace_7511251 : CollatzResearch.WordTrace tailWord_7511251 prefixEnd_7511251 3856882079564496929618891 := by
  unfold tailWord_7511251
  simp only [CollatzResearch.WordTrace]
  refine ⟨273957830511027921385429607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182638553674018614256953071 273957830511027921385429607)
  ·
    refine ⟨410936745766541882078144411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273957830511027921385429607 410936745766541882078144411)
    ·
      refine ⟨616405118649812823117216617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410936745766541882078144411 616405118649812823117216617)
      ·
        refine ⟨462303838987359617337912463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616405118649812823117216617 462303838987359617337912463)
        ·
          refine ⟨693455758481039426006868695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462303838987359617337912463 693455758481039426006868695)
          ·
            refine ⟨1040183637721559139010303043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693455758481039426006868695 1040183637721559139010303043)
            ·
              refine ⟨1560275456582338708515454565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040183637721559139010303043 1560275456582338708515454565)
              ·
                refine ⟨292551648109188507846647731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1560275456582338708515454565 292551648109188507846647731)
                ·
                  refine ⟨438827472163782761769971597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292551648109188507846647731 438827472163782761769971597)
                  ·
                    refine ⟨164560302061418535663739349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 438827472163782761769971597 164560302061418535663739349)
                    ·
                      refine ⟨3856882079564496929618891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164560302061418535663739349 3856882079564496929618891)
                      ·
                        rfl

theorem cell23_7511251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_7511251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511251 prefixEnd_7511251 := by exact prefixLift 7511251
  have htrace : WordTrace (prefixWord ++ tailWord_7511251) baseStart_7511251 baseEnd_7511251 := by
    simpa [prefixWord, tailWord_7511251, baseEnd_7511251] using wordTrace_append hprefix tailTrace_7511251
  have hstable : (prefixWord ++ tailWord_7511251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511251).length < 2 ^ (prefixWord ++ tailWord_7511251).sum := by decide
  have hdescent : baseEnd_7511251 < baseStart_7511251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511272 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_7511272 : Nat := 118140960795 + 7511272 * 2 ^ 59
def prefixEnd_7511272 : Nat := 4983230072969 + 3 ^ 40 * 7511272 * 2
def baseEnd_7511272 : Nat := 3856892862658241347456295

theorem tailTrace_7511272 : CollatzResearch.WordTrace tailWord_7511272 prefixEnd_7511272 3856892862658241347456295 := by
  unfold tailWord_7511272
  simp only [CollatzResearch.WordTrace]
  refine ⟨136979298221975920985972035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182639064295967894647962713 136979298221975920985972035)
  ·
    refine ⟨205468947332963881478958053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136979298221975920985972035 205468947332963881478958053)
    ·
      refine ⟨38525427624930727777304635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205468947332963881478958053 38525427624930727777304635)
      ·
        refine ⟨57788141437396091665956953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38525427624930727777304635 57788141437396091665956953)
        ·
          refine ⟨43341106078047068749467715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57788141437396091665956953 43341106078047068749467715)
          ·
            refine ⟨65011659117070603124201573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43341106078047068749467715 65011659117070603124201573)
            ·
              refine ⟨12189686084450738085787795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65011659117070603124201573 12189686084450738085787795)
              ·
                refine ⟨18284529126676107128681693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12189686084450738085787795 18284529126676107128681693)
                ·
                  refine ⟨6856698422503540173255635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18284529126676107128681693 6856698422503540173255635)
                  ·
                    refine ⟨10285047633755310259883453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6856698422503540173255635 10285047633755310259883453)
                    ·
                      refine ⟨3856892862658241347456295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285047633755310259883453 3856892862658241347456295)
                      ·
                        rfl

theorem cell23_7511272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_7511272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511272 prefixEnd_7511272 := by exact prefixLift 7511272
  have htrace : WordTrace (prefixWord ++ tailWord_7511272) baseStart_7511272 baseEnd_7511272 := by
    simpa [prefixWord, tailWord_7511272, baseEnd_7511272] using wordTrace_append hprefix tailTrace_7511272
  have hstable : (prefixWord ++ tailWord_7511272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511272).length < 2 ^ (prefixWord ++ tailWord_7511272).sum := by decide
  have hdescent : baseEnd_7511272 < baseStart_7511272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511292 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_7511292 : Nat := 118140960795 + 7511292 * 2 ^ 59
def prefixEnd_7511292 : Nat := 4983230072969 + 3 ^ 40 * 7511292 * 2
def baseEnd_7511292 : Nat := 1285634377423777089735401

theorem tailTrace_7511292 : CollatzResearch.WordTrace tailWord_7511292 prefixEnd_7511292 1285634377423777089735401 := by
  unfold tailWord_7511292
  simp only [CollatzResearch.WordTrace]
  refine ⟨136979662951939692693836065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182639550602586256925114753 136979662951939692693836065)
  ·
    refine ⟨102734747213954769520377049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136979662951939692693836065 102734747213954769520377049)
    ·
      refine ⟨77051060410466077140282787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102734747213954769520377049 77051060410466077140282787)
      ·
        refine ⟨115576590615699115710424181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77051060410466077140282787 115576590615699115710424181)
        ·
          refine ⟨10835305370221792097852267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115576590615699115710424181 10835305370221792097852267)
          ·
            refine ⟨16252958055332688146778401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10835305370221792097852267 16252958055332688146778401)
            ·
              refine ⟨12189718541499516110083801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16252958055332688146778401 12189718541499516110083801)
              ·
                refine ⟨9142288906124637082562851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12189718541499516110083801 9142288906124637082562851)
                ·
                  refine ⟨13713433359186955623844277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9142288906124637082562851 13713433359186955623844277)
                  ·
                    refine ⟨1285634377423777089735401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13713433359186955623844277 1285634377423777089735401)
                    ·
                      rfl

theorem cell23_7511292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_7511292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511292 prefixEnd_7511292 := by exact prefixLift 7511292
  have htrace : WordTrace (prefixWord ++ tailWord_7511292) baseStart_7511292 baseEnd_7511292 := by
    simpa [prefixWord, tailWord_7511292, baseEnd_7511292] using wordTrace_append hprefix tailTrace_7511292
  have hstable : (prefixWord ++ tailWord_7511292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511292).length < 2 ^ (prefixWord ++ tailWord_7511292).sum := by decide
  have hdescent : baseEnd_7511292 < baseStart_7511292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511295 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 4]
def baseStart_7511295 : Nat := 118140960795 + 7511295 * 2 ^ 59
def prefixEnd_7511295 : Nat := 4983230072969 + 3 ^ 40 * 7511295 * 2
def baseEnd_7511295 : Nat := 3856904672713294757468689

theorem tailTrace_7511295 : CollatzResearch.WordTrace tailWord_7511295 prefixEnd_7511295 3856904672713294757468689 := by
  unfold tailWord_7511295
  simp only [CollatzResearch.WordTrace]
  refine ⟨273959435322868516900031339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182639623548579011266687559 273959435322868516900031339)
  ·
    refine ⟨410939152984302775350047009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273959435322868516900031339 410939152984302775350047009)
    ·
      refine ⟨308204364738227081512535257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410939152984302775350047009 308204364738227081512535257)
      ·
        refine ⟨231153273553670311134401443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308204364738227081512535257 231153273553670311134401443)
        ·
          refine ⟨346729910330505466701602165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231153273553670311134401443 346729910330505466701602165)
          ·
            refine ⟨32505929093484887503275203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 346729910330505466701602165 32505929093484887503275203)
            ·
              refine ⟨48758893640227331254912805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32505929093484887503275203 48758893640227331254912805)
              ·
                refine ⟨9142292557542624610296151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48758893640227331254912805 9142292557542624610296151)
                ·
                  refine ⟨13713438836313936915444227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9142292557542624610296151 13713438836313936915444227)
                  ·
                    refine ⟨20570158254470905373166341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13713438836313936915444227 20570158254470905373166341)
                    ·
                      refine ⟨3856904672713294757468689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20570158254470905373166341 3856904672713294757468689)
                      ·
                        rfl

theorem cell23_7511295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_7511295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511295 prefixEnd_7511295 := by exact prefixLift 7511295
  have htrace : WordTrace (prefixWord ++ tailWord_7511295) baseStart_7511295 baseEnd_7511295 := by
    simpa [prefixWord, tailWord_7511295, baseEnd_7511295] using wordTrace_append hprefix tailTrace_7511295
  have hstable : (prefixWord ++ tailWord_7511295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511295).length < 2 ^ (prefixWord ++ tailWord_7511295).sum := by decide
  have hdescent : baseEnd_7511295 < baseStart_7511295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511325 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_7511325 : Nat := 118140960795 + 7511325 * 2 ^ 59
def prefixEnd_7511325 : Nat := 4983230072969 + 3 ^ 40 * 7511325 * 2
def baseEnd_7511325 : Nat := 3856920077132929640093551

theorem tailTrace_7511325 : CollatzResearch.WordTrace tailWord_7511325 prefixEnd_7511325 3856920077132929640093551 := by
  unfold tailWord_7511325
  simp only [CollatzResearch.WordTrace]
  refine ⟨273960529512759832023623429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182640353008506554682415619 273960529512759832023623429)
  ·
    refine ⟨51367599283642468504429393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273960529512759832023623429 51367599283642468504429393)
    ·
      refine ⟨38525699462731851378322045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51367599283642468504429393 38525699462731851378322045)
      ·
        refine ⟨14447137298524444266870767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38525699462731851378322045 14447137298524444266870767)
        ·
          refine ⟨21670705947786666400306151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14447137298524444266870767 21670705947786666400306151)
          ·
            refine ⟨32506058921679999600459227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21670705947786666400306151 32506058921679999600459227)
            ·
              refine ⟨48759088382519999400688841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32506058921679999600459227 48759088382519999400688841)
              ·
                refine ⟨36569316286889999550516631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48759088382519999400688841 36569316286889999550516631)
                ·
                  refine ⟨54853974430334999325774947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36569316286889999550516631 54853974430334999325774947)
                  ·
                    refine ⟨82280961645502498988662421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54853974430334999325774947 82280961645502498988662421)
                    ·
                      refine ⟨3856920077132929640093551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82280961645502498988662421 3856920077132929640093551)
                      ·
                        rfl

theorem cell23_7511325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_7511325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511325 prefixEnd_7511325 := by exact prefixLift 7511325
  have htrace : WordTrace (prefixWord ++ tailWord_7511325) baseStart_7511325 baseEnd_7511325 := by
    simpa [prefixWord, tailWord_7511325, baseEnd_7511325] using wordTrace_append hprefix tailTrace_7511325
  have hstable : (prefixWord ++ tailWord_7511325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511325).length < 2 ^ (prefixWord ++ tailWord_7511325).sum := by decide
  have hdescent : baseEnd_7511325 < baseStart_7511325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511349 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_7511349 : Nat := 118140960795 + 7511349 * 2 ^ 59
def prefixEnd_7511349 : Nat := 4983230072969 + 3 ^ 40 * 7511349 * 2
def baseEnd_7511349 : Nat := 3856932400668637546193441

theorem tailTrace_7511349 : CollatzResearch.WordTrace tailWord_7511349 prefixEnd_7511349 3856932400668637546193441 := by
  unfold tailWord_7511349
  simp only [CollatzResearch.WordTrace]
  refine ⟨273961404864672884122497101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182640936576448589414998067 273961404864672884122497101)
  ·
    refine ⟨102735526824252331545936413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 273961404864672884122497101 102735526824252331545936413)
    ·
      refine ⟨38525822559094624329726155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102735526824252331545936413 38525822559094624329726155)
      ·
        refine ⟨57788733838641936494589233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38525822559094624329726155 57788733838641936494589233)
        ·
          refine ⟨43341550378981452370941925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57788733838641936494589233 43341550378981452370941925)
          ·
            refine ⟨8126540696059022319551611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43341550378981452370941925 8126540696059022319551611)
            ·
              refine ⟨12189811044088533479327417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126540696059022319551611 12189811044088533479327417)
              ·
                refine ⟨9142358283066400109495563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12189811044088533479327417 9142358283066400109495563)
                ·
                  refine ⟨13713537424599600164243345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9142358283066400109495563 13713537424599600164243345)
                  ·
                    refine ⟨10285153068449700123182509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13713537424599600164243345 10285153068449700123182509)
                    ·
                      refine ⟨3856932400668637546193441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285153068449700123182509 3856932400668637546193441)
                      ·
                        rfl

theorem cell23_7511349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_7511349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511349 prefixEnd_7511349 := by exact prefixLift 7511349
  have htrace : WordTrace (prefixWord ++ tailWord_7511349) baseStart_7511349 baseEnd_7511349 := by
    simpa [prefixWord, tailWord_7511349, baseEnd_7511349] using wordTrace_append hprefix tailTrace_7511349
  have hstable : (prefixWord ++ tailWord_7511349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511349).length < 2 ^ (prefixWord ++ tailWord_7511349).sum := by decide
  have hdescent : baseEnd_7511349 < baseStart_7511349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511395 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 2, 6]
def baseStart_7511395 : Nat := 118140960795 + 7511395 * 2 ^ 59
def prefixEnd_7511395 : Nat := 4983230072969 + 3 ^ 40 * 7511395 * 2
def baseEnd_7511395 : Nat := 1285652006926248122072743

theorem tailTrace_7511395 : CollatzResearch.WordTrace tailWord_7511395 prefixEnd_7511395 1285652006926248122072743 := by
  unfold tailWord_7511395
  simp only [CollatzResearch.WordTrace]
  refine ⟨273963082622506233978671639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182642055081670822652447759 273963082622506233978671639)
  ·
    refine ⟨410944623933759350968007459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273963082622506233978671639 410944623933759350968007459)
    ·
      refine ⟨616416935900639026452011189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410944623933759350968007459 616416935900639026452011189)
      ·
        refine ⟨57789087740684908729876049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 616416935900639026452011189 57789087740684908729876049)
        ·
          refine ⟨43341815805513681547407037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57789087740684908729876049 43341815805513681547407037)
          ·
            refine ⟨16253180927067630580277639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43341815805513681547407037 16253180927067630580277639)
            ·
              refine ⟨24379771390601445870416459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16253180927067630580277639 24379771390601445870416459)
              ·
                refine ⟨36569657085902168805624689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24379771390601445870416459 36569657085902168805624689)
                ·
                  refine ⟨27427242814426626604218517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36569657085902168805624689 27427242814426626604218517)
                  ·
                    refine ⟨1285652006926248122072743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27427242814426626604218517 1285652006926248122072743)
                    ·
                      rfl

theorem cell23_7511395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 6].length) (baseStart_7511395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511395 prefixEnd_7511395 := by exact prefixLift 7511395
  have htrace : WordTrace (prefixWord ++ tailWord_7511395) baseStart_7511395 baseEnd_7511395 := by
    simpa [prefixWord, tailWord_7511395, baseEnd_7511395] using wordTrace_append hprefix tailTrace_7511395
  have hstable : (prefixWord ++ tailWord_7511395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511395).length < 2 ^ (prefixWord ++ tailWord_7511395).sum := by decide
  have hdescent : baseEnd_7511395 < baseStart_7511395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511435 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 3]
def baseStart_7511435 : Nat := 118140960795 + 7511435 * 2 ^ 59
def prefixEnd_7511435 : Nat := 4983230072969 + 3 ^ 40 * 7511435 * 2
def baseEnd_7511435 : Nat := 3856976560004924209718045

theorem tailTrace_7511435 : CollatzResearch.WordTrace tailWord_7511435 prefixEnd_7511435 3856976560004924209718045 := by
  unfold tailWord_7511435
  simp only [CollatzResearch.WordTrace]
  refine ⟨273964541542361320810127759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182643027694907547206751839 273964541542361320810127759)
  ·
    refine ⟨410946812313541981215191639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273964541542361320810127759 410946812313541981215191639)
    ·
      refine ⟨616420218470312971822787459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410946812313541981215191639 616420218470312971822787459)
      ·
        refine ⟨924630327705469457734181189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616420218470312971822787459 924630327705469457734181189)
        ·
          refine ⟨173368186444775523325158973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 924630327705469457734181189 173368186444775523325158973)
          ·
            refine ⟨65013069916790821246934615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173368186444775523325158973 65013069916790821246934615)
            ·
              refine ⟨97519604875186231870401923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65013069916790821246934615 97519604875186231870401923)
              ·
                refine ⟨146279407312779347805602885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97519604875186231870401923 146279407312779347805602885)
                ·
                  refine ⟨27427388871146127713550541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146279407312779347805602885 27427388871146127713550541)
                  ·
                    refine ⟨10285270826679797892581453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27427388871146127713550541 10285270826679797892581453)
                    ·
                      refine ⟨3856976560004924209718045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285270826679797892581453 3856976560004924209718045)
                      ·
                        rfl

theorem cell23_7511435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 3].length) (baseStart_7511435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511435 prefixEnd_7511435 := by exact prefixLift 7511435
  have htrace : WordTrace (prefixWord ++ tailWord_7511435) baseStart_7511435 baseEnd_7511435 := by
    simpa [prefixWord, tailWord_7511435, baseEnd_7511435] using wordTrace_append hprefix tailTrace_7511435
  have hstable : (prefixWord ++ tailWord_7511435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511435).length < 2 ^ (prefixWord ++ tailWord_7511435).sum := by decide
  have hdescent : baseEnd_7511435 < baseStart_7511435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511453 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_7511453 : Nat := 118140960795 + 7511453 * 2 ^ 59
def prefixEnd_7511453 : Nat := 4983230072969 + 3 ^ 40 * 7511453 * 2
def baseEnd_7511453 : Nat := 3856985802656705139292963

theorem tailTrace_7511453 : CollatzResearch.WordTrace tailWord_7511453 prefixEnd_7511453 3856985802656705139292963 := by
  unfold tailWord_7511453
  simp only [CollatzResearch.WordTrace]
  refine ⟨273965198056296109884283013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182643465370864073256188675 273965198056296109884283013)
  ·
    refine ⟨51368474635555520603303065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273965198056296109884283013 51368474635555520603303065)
    ·
      refine ⟨38526355976666640452477299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51368474635555520603303065 38526355976666640452477299)
      ·
        refine ⟨57789533964999960678715949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38526355976666640452477299 57789533964999960678715949)
        ·
          refine ⟨21671075236874985254518481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57789533964999960678715949 21671075236874985254518481)
          ·
            refine ⟨16253306427656238940888861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21671075236874985254518481 16253306427656238940888861)
            ·
              refine ⟨6094989910371089602833323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16253306427656238940888861 6094989910371089602833323)
              ·
                refine ⟨9142484865556634404249985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094989910371089602833323 9142484865556634404249985)
                ·
                  refine ⟨6856863649167475803187489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9142484865556634404249985 6856863649167475803187489)
                  ·
                    refine ⟨5142647736875606852390617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6856863649167475803187489 5142647736875606852390617)
                    ·
                      refine ⟨3856985802656705139292963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5142647736875606852390617 3856985802656705139292963)
                      ·
                        rfl

theorem cell23_7511453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_7511453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511453 prefixEnd_7511453 := by exact prefixLift 7511453
  have htrace : WordTrace (prefixWord ++ tailWord_7511453) baseStart_7511453 baseEnd_7511453 := by
    simpa [prefixWord, tailWord_7511453, baseEnd_7511453] using wordTrace_append hprefix tailTrace_7511453
  have hstable : (prefixWord ++ tailWord_7511453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511453).length < 2 ^ (prefixWord ++ tailWord_7511453).sum := by decide
  have hdescent : baseEnd_7511453 < baseStart_7511453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511455 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 1, 7]
def baseStart_7511455 : Nat := 118140960795 + 7511455 * 2 ^ 59
def prefixEnd_7511455 : Nat := 4983230072969 + 3 ^ 40 * 7511455 * 2
def baseEnd_7511455 : Nat := 1285662276539338043822651

theorem tailTrace_7511455 : CollatzResearch.WordTrace tailWord_7511455 prefixEnd_7511455 1285662276539338043822651 := by
  unfold tailWord_7511455
  simp only [CollatzResearch.WordTrace]
  refine ⟨273965271002288864225855819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182643514001525909483903879 273965271002288864225855819)
  ·
    refine ⟨410947906503433296338783729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273965271002288864225855819 410947906503433296338783729)
    ·
      refine ⟨308210929877574972254087797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410947906503433296338783729 308210929877574972254087797)
      ·
        refine ⟨28894774676022653648820731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308210929877574972254087797 28894774676022653648820731)
        ·
          refine ⟨43342162014033980473231097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28894774676022653648820731 43342162014033980473231097)
          ·
            refine ⟨32506621510525485354923323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43342162014033980473231097 32506621510525485354923323)
            ·
              refine ⟨48759932265788228032384985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32506621510525485354923323 48759932265788228032384985)
              ·
                refine ⟨36569949199341171024288739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48759932265788228032384985 36569949199341171024288739)
                ·
                  refine ⟨54854923799011756536433109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36569949199341171024288739 54854923799011756536433109)
                  ·
                    refine ⟨1285662276539338043822651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54854923799011756536433109 1285662276539338043822651)
                    ·
                      rfl

theorem cell23_7511455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_7511455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511455 prefixEnd_7511455 := by exact prefixLift 7511455
  have htrace : WordTrace (prefixWord ++ tailWord_7511455) baseStart_7511455 baseEnd_7511455 := by
    simpa [prefixWord, tailWord_7511455, baseEnd_7511455] using wordTrace_append hprefix tailTrace_7511455
  have hstable : (prefixWord ++ tailWord_7511455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511455).length < 2 ^ (prefixWord ++ tailWord_7511455).sum := by decide
  have hdescent : baseEnd_7511455 < baseStart_7511455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511475 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 4]
def baseStart_7511475 : Nat := 118140960795 + 7511475 * 2 ^ 59
def prefixEnd_7511475 : Nat := 4983230072969 + 3 ^ 40 * 7511475 * 2
def baseEnd_7511475 : Nat := 3856997099231104053217861

theorem tailTrace_7511475 : CollatzResearch.WordTrace tailWord_7511475 prefixEnd_7511475 3856997099231104053217861 := by
  unfold tailWord_7511475
  simp only [CollatzResearch.WordTrace]
  refine ⟨273966000462216407641583879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182644000308144271761055919 273966000462216407641583879)
  ·
    refine ⟨410949000693324611462375819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273966000462216407641583879 410949000693324611462375819)
    ·
      refine ⟨616423501039986917193563729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410949000693324611462375819 616423501039986917193563729)
      ·
        refine ⟨462317625779990187895172797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616423501039986917193563729 462317625779990187895172797)
        ·
          refine ⟨173369109667496320460689799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462317625779990187895172797 173369109667496320460689799)
          ·
            refine ⟨260053664501244480691034699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173369109667496320460689799 260053664501244480691034699)
            ·
              refine ⟨390080496751866721036552049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260053664501244480691034699 390080496751866721036552049)
              ·
                refine ⟨292560372563900040777414037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390080496751866721036552049 292560372563900040777414037)
                ·
                  refine ⟨13713767463932814411441283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 292560372563900040777414037 13713767463932814411441283)
                  ·
                    refine ⟨20570651195899221617161925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13713767463932814411441283 20570651195899221617161925)
                    ·
                      refine ⟨3856997099231104053217861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20570651195899221617161925 3856997099231104053217861)
                      ·
                        rfl

theorem cell23_7511475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_7511475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511475 prefixEnd_7511475 := by exact prefixLift 7511475
  have htrace : WordTrace (prefixWord ++ tailWord_7511475) baseStart_7511475 baseEnd_7511475 := by
    simpa [prefixWord, tailWord_7511475, baseEnd_7511475] using wordTrace_append hprefix tailTrace_7511475
  have hstable : (prefixWord ++ tailWord_7511475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511475).length < 2 ^ (prefixWord ++ tailWord_7511475).sum := by decide
  have hdescent : baseEnd_7511475 < baseStart_7511475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511562 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_7511562 : Nat := 118140960795 + 7511562 * 2 ^ 59
def prefixEnd_7511562 : Nat := 4983230072969 + 3 ^ 40 * 7511562 * 2
def baseEnd_7511562 : Nat := 1285680590682681737609987

theorem tailTrace_7511562 : CollatzResearch.WordTrace tailWord_7511562 prefixEnd_7511562 1285680590682681737609987 := by
  unfold tailWord_7511562
  simp only [CollatzResearch.WordTrace]
  refine ⟨68492293403225305375000235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182646115741934147666667293 68492293403225305375000235)
  ·
    refine ⟨102738440104837958062500353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68492293403225305375000235 102738440104837958062500353)
    ·
      refine ⟨77053830078628468546875265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102738440104837958062500353 77053830078628468546875265)
      ·
        refine ⟨57790372558971351410156449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77053830078628468546875265 57790372558971351410156449)
        ·
          refine ⟨43342779419228513557617337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57790372558971351410156449 43342779419228513557617337)
          ·
            refine ⟨32507084564421385168213003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43342779419228513557617337 32507084564421385168213003)
            ·
              refine ⟨48760626846632077752319505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32507084564421385168213003 48760626846632077752319505)
              ·
                refine ⟨36570470134974058314239629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48760626846632077752319505 36570470134974058314239629)
                ·
                  refine ⟨13713926300615271867839861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36570470134974058314239629 13713926300615271867839861)
                  ·
                    refine ⟨1285680590682681737609987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13713926300615271867839861 1285680590682681737609987)
                    ·
                      rfl

theorem cell23_7511562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_7511562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511562 prefixEnd_7511562 := by exact prefixLift 7511562
  have htrace : WordTrace (prefixWord ++ tailWord_7511562) baseStart_7511562 baseEnd_7511562 := by
    simpa [prefixWord, tailWord_7511562, baseEnd_7511562] using wordTrace_append hprefix tailTrace_7511562
  have hstable : (prefixWord ++ tailWord_7511562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511562).length < 2 ^ (prefixWord ++ tailWord_7511562).sum := by decide
  have hdescent : baseEnd_7511562 < baseStart_7511562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511576 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 3, 1, 3]
def baseStart_7511576 : Nat := 118140960795 + 7511576 * 2 ^ 59
def prefixEnd_7511576 : Nat := 4983230072969 + 3 ^ 40 * 7511576 * 2
def baseEnd_7511576 : Nat := 3857048960777208158054897

theorem tailTrace_7511576 : CollatzResearch.WordTrace tailWord_7511576 prefixEnd_7511576 3857048960777208158054897 := by
  unfold tailWord_7511576
  simp only [CollatzResearch.WordTrace]
  refine ⟨136984842117425250945505291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182646456156567001260673721 136984842117425250945505291)
  ·
    refine ⟨205477263176137876418257937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136984842117425250945505291 205477263176137876418257937)
    ·
      refine ⟨154107947382103407313693453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205477263176137876418257937 154107947382103407313693453)
      ·
        refine ⟨57790480268288777742635045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154107947382103407313693453 57790480268288777742635045)
        ·
          refine ⟨10835715050304145826744071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57790480268288777742635045 10835715050304145826744071)
          ·
            refine ⟨16253572575456218740116107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10835715050304145826744071 16253572575456218740116107)
            ·
              refine ⟨24380358863184328110174161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16253572575456218740116107 24380358863184328110174161)
              ·
                refine ⟨18285269147388246082630621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24380358863184328110174161 18285269147388246082630621)
                ·
                  refine ⟨6856975930270592280986483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18285269147388246082630621 6856975930270592280986483)
                  ·
                    refine ⟨10285463895405888421479725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6856975930270592280986483 10285463895405888421479725)
                    ·
                      refine ⟨3857048960777208158054897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285463895405888421479725 3857048960777208158054897)
                      ·
                        rfl

theorem cell23_7511576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_7511576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511576 prefixEnd_7511576 := by exact prefixLift 7511576
  have htrace : WordTrace (prefixWord ++ tailWord_7511576) baseStart_7511576 baseEnd_7511576 := by
    simpa [prefixWord, tailWord_7511576, baseEnd_7511576] using wordTrace_append hprefix tailTrace_7511576
  have hstable : (prefixWord ++ tailWord_7511576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511576).length < 2 ^ (prefixWord ++ tailWord_7511576).sum := by decide
  have hdescent : baseEnd_7511576 < baseStart_7511576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511586 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_7511586 : Nat := 118140960795 + 7511586 * 2 ^ 59
def prefixEnd_7511586 : Nat := 4983230072969 + 3 ^ 40 * 7511586 * 2
def baseEnd_7511586 : Nat := 3857054095583753118929851

theorem tailTrace_7511586 : CollatzResearch.WordTrace tailWord_7511586 prefixEnd_7511586 3857054095583753118929851 := by
  unfold tailWord_7511586
  simp only [CollatzResearch.WordTrace]
  refine ⟨68492512241203568399718653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182646699309876182399249741 68492512241203568399718653)
  ·
    refine ⟨25684692090451338149894495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68492512241203568399718653 25684692090451338149894495)
    ·
      refine ⟨38527038135677007224841743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25684692090451338149894495 38527038135677007224841743)
      ·
        refine ⟨57790557203515510837262615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38527038135677007224841743 57790557203515510837262615)
        ·
          refine ⟨86685835805273266255893923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57790557203515510837262615 86685835805273266255893923)
          ·
            refine ⟨130028753707909899383840885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86685835805273266255893923 130028753707909899383840885)
            ·
              refine ⟨12190195660116553067235083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130028753707909899383840885 12190195660116553067235083)
              ·
                refine ⟨18285293490174829600852625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12190195660116553067235083 18285293490174829600852625)
                ·
                  refine ⟨13713970117631122200639469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18285293490174829600852625 13713970117631122200639469)
                  ·
                    refine ⟨5142738794111670825239801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13713970117631122200639469 5142738794111670825239801)
                    ·
                      refine ⟨3857054095583753118929851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5142738794111670825239801 3857054095583753118929851)
                      ·
                        rfl

theorem cell23_7511586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_7511586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511586 prefixEnd_7511586 := by exact prefixLift 7511586
  have htrace : WordTrace (prefixWord ++ tailWord_7511586) baseStart_7511586 baseEnd_7511586 := by
    simpa [prefixWord, tailWord_7511586, baseEnd_7511586] using wordTrace_append hprefix tailTrace_7511586
  have hstable : (prefixWord ++ tailWord_7511586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511586).length < 2 ^ (prefixWord ++ tailWord_7511586).sum := by decide
  have hdescent : baseEnd_7511586 < baseStart_7511586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511595 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 6]
def baseStart_7511595 : Nat := 118140960795 + 7511595 * 2 ^ 59
def prefixEnd_7511595 : Nat := 4983230072969 + 3 ^ 40 * 7511595 * 2
def baseEnd_7511595 : Nat := 3857058716909643583717309

theorem tailTrace_7511595 : CollatzResearch.WordTrace tailWord_7511595 prefixEnd_7511595 3857058716909643583717309 := by
  unfold tailWord_7511595
  simp only [CollatzResearch.WordTrace]
  refine ⟨273970377221781668135952239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182646918147854445423968159 273970377221781668135952239)
  ·
    refine ⟨410955565832672502203928359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273970377221781668135952239 410955565832672502203928359)
    ·
      refine ⟨616433348749008753305892539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410955565832672502203928359 616433348749008753305892539)
      ·
        refine ⟨924650023123513129958838809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616433348749008753305892539 924650023123513129958838809)
        ·
          refine ⟨693487517342634847469129107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924650023123513129958838809 693487517342634847469129107)
          ·
            refine ⟨1040231276013952271203693661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693487517342634847469129107 1040231276013952271203693661)
            ·
              refine ⟨390086728505232101701385123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040231276013952271203693661 390086728505232101701385123)
              ·
                refine ⟨585130092757848152552077685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390086728505232101701385123 585130092757848152552077685)
                ·
                  refine ⟨54855946196048264301757283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 585130092757848152552077685 54855946196048264301757283)
                  ·
                    refine ⟨82283919294072396452635925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54855946196048264301757283 82283919294072396452635925)
                    ·
                      refine ⟨3857058716909643583717309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82283919294072396452635925 3857058716909643583717309)
                      ·
                        rfl

theorem cell23_7511595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_7511595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511595 prefixEnd_7511595 := by exact prefixLift 7511595
  have htrace : WordTrace (prefixWord ++ tailWord_7511595) baseStart_7511595 baseEnd_7511595 := by
    simpa [prefixWord, tailWord_7511595, baseEnd_7511595] using wordTrace_append hprefix tailTrace_7511595
  have hstable : (prefixWord ++ tailWord_7511595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511595).length < 2 ^ (prefixWord ++ tailWord_7511595).sum := by decide
  have hdescent : baseEnd_7511595 < baseStart_7511595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511602 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_7511602 : Nat := 118140960795 + 7511602 * 2 ^ 59
def prefixEnd_7511602 : Nat := 4983230072969 + 3 ^ 40 * 7511602 * 2
def baseEnd_7511602 : Nat := 3857062311274225056329777

theorem tailTrace_7511602 : CollatzResearch.WordTrace tailWord_7511602 prefixEnd_7511602 3857062311274225056329777 := by
  unfold tailWord_7511602
  simp only [CollatzResearch.WordTrace]
  refine ⟨68492658133189077082864265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182647088355170872220971373 68492658133189077082864265)
  ·
    refine ⟨51369493599891807812148199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68492658133189077082864265 51369493599891807812148199)
    ·
      refine ⟨77054240399837711718222299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51369493599891807812148199 77054240399837711718222299)
      ·
        refine ⟨115581360599756567577333449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77054240399837711718222299 115581360599756567577333449)
        ·
          refine ⟨86686020449817425683000087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115581360599756567577333449 86686020449817425683000087)
          ·
            refine ⟨130029030674726138524500131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86686020449817425683000087 130029030674726138524500131)
            ·
              refine ⟨195043546012089207786750197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130029030674726138524500131 195043546012089207786750197)
              ·
                refine ⟨18285332438633363230007831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195043546012089207786750197 18285332438633363230007831)
                ·
                  refine ⟨27427998657950044845011747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18285332438633363230007831 27427998657950044845011747)
                  ·
                    refine ⟨41141997986925067267517621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27427998657950044845011747 41141997986925067267517621)
                    ·
                      refine ⟨3857062311274225056329777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41141997986925067267517621 3857062311274225056329777)
                      ·
                        rfl

theorem cell23_7511602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_7511602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511602 prefixEnd_7511602 := by exact prefixLift 7511602
  have htrace : WordTrace (prefixWord ++ tailWord_7511602) baseStart_7511602 baseEnd_7511602 := by
    simpa [prefixWord, tailWord_7511602, baseEnd_7511602] using wordTrace_append hprefix tailTrace_7511602
  have hstable : (prefixWord ++ tailWord_7511602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511602).length < 2 ^ (prefixWord ++ tailWord_7511602).sum := by decide
  have hdescent : baseEnd_7511602 < baseStart_7511602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511609 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 4, 4]
def baseStart_7511609 : Nat := 118140960795 + 7511609 * 2 ^ 59
def prefixEnd_7511609 : Nat := 4983230072969 + 3 ^ 40 * 7511609 * 2
def baseEnd_7511609 : Nat := 1285688635212935509647415

theorem tailTrace_7511609 : CollatzResearch.WordTrace tailWord_7511609 prefixEnd_7511609 1285688635212935509647415 := by
  unfold tailWord_7511609
  simp only [CollatzResearch.WordTrace]
  refine ⟨273970887843730948526961881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182647258562487299017974587 273970887843730948526961881)
  ·
    refine ⟨205478165882798211395221411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273970887843730948526961881 205478165882798211395221411)
    ·
      refine ⟨308217248824197317092832117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205478165882798211395221411 308217248824197317092832117)
      ·
        refine ⟨28895367077268498477453011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308217248824197317092832117 28895367077268498477453011)
        ·
          refine ⟨43343050615902747716179517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28895367077268498477453011 43343050615902747716179517)
          ·
            refine ⟨16253643980963530393567319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43343050615902747716179517 16253643980963530393567319)
            ·
              refine ⟨24380465971445295590350979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16253643980963530393567319 24380465971445295590350979)
              ·
                refine ⟨36570698957167943385526469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24380465971445295590350979 36570698957167943385526469)
                ·
                  refine ⟨6857006054468989384786213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36570698957167943385526469 6857006054468989384786213)
                  ·
                    refine ⟨1285688635212935509647415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6857006054468989384786213 1285688635212935509647415)
                    ·
                      rfl

theorem cell23_7511609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 4].length) (baseStart_7511609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511609 prefixEnd_7511609 := by exact prefixLift 7511609
  have htrace : WordTrace (prefixWord ++ tailWord_7511609) baseStart_7511609 baseEnd_7511609 := by
    simpa [prefixWord, tailWord_7511609, baseEnd_7511609] using wordTrace_append hprefix tailTrace_7511609
  have hstable : (prefixWord ++ tailWord_7511609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511609).length < 2 ^ (prefixWord ++ tailWord_7511609).sum := by decide
  have hdescent : baseEnd_7511609 < baseStart_7511609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511626 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_7511626 : Nat := 118140960795 + 7511626 * 2 ^ 59
def prefixEnd_7511626 : Nat := 4983230072969 + 3 ^ 40 * 7511626 * 2
def baseEnd_7511626 : Nat := 1285691544936644320809889

theorem tailTrace_7511626 : CollatzResearch.WordTrace tailWord_7511626 prefixEnd_7511626 1285691544936644320809889 := by
  unfold tailWord_7511626
  simp only [CollatzResearch.WordTrace]
  refine ⟨68492876971167340107582683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182647671923112906953553821 68492876971167340107582683)
  ·
    refine ⟨102739315456751010161374025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68492876971167340107582683 102739315456751010161374025)
    ·
      refine ⟨77054486592563257621030519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102739315456751010161374025 77054486592563257621030519)
      ·
        refine ⟨115581729888844886431545779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77054486592563257621030519 115581729888844886431545779)
        ·
          refine ⟨173372594833267329647318669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115581729888844886431545779 173372594833267329647318669)
          ·
            refine ⟨65014723062475248617744501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173372594833267329647318669 65014723062475248617744501)
            ·
              refine ⟨6095130287107054557913547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65014723062475248617744501 6095130287107054557913547)
              ·
                refine ⟨9142695430660581836870321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095130287107054557913547 9142695430660581836870321)
                ·
                  refine ⟨6857021572995436377652741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9142695430660581836870321 6857021572995436377652741)
                  ·
                    refine ⟨1285691544936644320809889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6857021572995436377652741 1285691544936644320809889)
                    ·
                      rfl

theorem cell23_7511626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_7511626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511626 prefixEnd_7511626 := by exact prefixLift 7511626
  have htrace : WordTrace (prefixWord ++ tailWord_7511626) baseStart_7511626 baseEnd_7511626 := by
    simpa [prefixWord, tailWord_7511626, baseEnd_7511626] using wordTrace_append hprefix tailTrace_7511626
  have hstable : (prefixWord ++ tailWord_7511626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511626).length < 2 ^ (prefixWord ++ tailWord_7511626).sum := by decide
  have hdescent : baseEnd_7511626 < baseStart_7511626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511636 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_7511636 : Nat := 118140960795 + 7511636 * 2 ^ 59
def prefixEnd_7511636 : Nat := 4983230072969 + 3 ^ 40 * 7511636 * 2
def baseEnd_7511636 : Nat := 3857079769616477923304621

theorem tailTrace_7511636 : CollatzResearch.WordTrace tailWord_7511636 prefixEnd_7511636 3857079769616477923304621 := by
  unfold tailWord_7511636
  simp only [CollatzResearch.WordTrace]
  refine ⟨136985936307316566069097381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182647915076422088092129841 136985936307316566069097381)
  ·
    refine ⟨25684863057621856137955759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136985936307316566069097381 25684863057621856137955759)
    ·
      refine ⟨38527294586432784206933639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25684863057621856137955759 38527294586432784206933639)
      ·
        refine ⟨57790941879649176310400459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38527294586432784206933639 57790941879649176310400459)
        ·
          refine ⟨86686412819473764465600689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57790941879649176310400459 86686412819473764465600689)
          ·
            refine ⟨65014809614605323349200517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86686412819473764465600689 65014809614605323349200517)
            ·
              refine ⟨12190276802738498127975097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65014809614605323349200517 12190276802738498127975097)
              ·
                refine ⟨9142707602053873595981323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12190276802738498127975097 9142707602053873595981323)
                ·
                  refine ⟨13714061403080810393971985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9142707602053873595981323 13714061403080810393971985)
                  ·
                    refine ⟨10285546052310607795478989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13714061403080810393971985 10285546052310607795478989)
                    ·
                      refine ⟨3857079769616477923304621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285546052310607795478989 3857079769616477923304621)
                      ·
                        rfl

theorem cell23_7511636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_7511636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511636 prefixEnd_7511636 := by exact prefixLift 7511636
  have htrace : WordTrace (prefixWord ++ tailWord_7511636) baseStart_7511636 baseEnd_7511636 := by
    simpa [prefixWord, tailWord_7511636, baseEnd_7511636] using wordTrace_append hprefix tailTrace_7511636
  have hstable : (prefixWord ++ tailWord_7511636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511636).length < 2 ^ (prefixWord ++ tailWord_7511636).sum := by decide
  have hdescent : baseEnd_7511636 < baseStart_7511636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511639 : List Nat := [1, 1, 3, 2, 2, 5, 2, 7]
def baseStart_7511639 : Nat := 118140960795 + 7511639 * 2 ^ 59
def prefixEnd_7511639 : Nat := 4983230072969 + 3 ^ 40 * 7511639 * 2
def baseEnd_7511639 : Nat := 142854863335497830058041

theorem tailTrace_7511639 : CollatzResearch.WordTrace tailWord_7511639 prefixEnd_7511639 142854863335497830058041 := by
  unfold tailWord_7511639
  simp only [CollatzResearch.WordTrace]
  refine ⟨273971982033622263650553971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182647988022414842433702647 273971982033622263650553971)
  ·
    refine ⟨410957973050433395475830957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273971982033622263650553971 410957973050433395475830957)
    ·
      refine ⟨154109239893912523303436609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410957973050433395475830957 154109239893912523303436609)
      ·
        refine ⟨115581929920434392477577457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154109239893912523303436609 115581929920434392477577457)
        ·
          refine ⟨86686447440325794358183093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115581929920434392477577457 86686447440325794358183093)
          ·
            refine ⟨8126854447530543221079665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86686447440325794358183093 8126854447530543221079665)
            ·
              refine ⟨6095140835647907415809749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8126854447530543221079665 6095140835647907415809749)
              ·
                refine ⟨142854863335497830058041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6095140835647907415809749 142854863335497830058041)
                ·
                  rfl

theorem cell23_7511639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 7].length) (baseStart_7511639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511639 prefixEnd_7511639 := by exact prefixLift 7511639
  have htrace : WordTrace (prefixWord ++ tailWord_7511639) baseStart_7511639 baseEnd_7511639 := by
    simpa [prefixWord, tailWord_7511639, baseEnd_7511639] using wordTrace_append hprefix tailTrace_7511639
  have hstable : (prefixWord ++ tailWord_7511639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511639).length < 2 ^ (prefixWord ++ tailWord_7511639).sum := by decide
  have hdescent : baseEnd_7511639 < baseStart_7511639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511649 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_7511649 : Nat := 118140960795 + 7511649 * 2 ^ 59
def prefixEnd_7511649 : Nat := 4983230072969 + 3 ^ 40 * 7511649 * 2
def baseEnd_7511649 : Nat := 3857086444864986372442061

theorem tailTrace_7511649 : CollatzResearch.WordTrace tailWord_7511649 prefixEnd_7511649 3857086444864986372442061 := by
  unfold tailWord_7511649
  simp only [CollatzResearch.WordTrace]
  refine ⟨273972346763586035358418001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182648231175724023572278667 273972346763586035358418001)
  ·
    refine ⟨205479260072689526518813501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273972346763586035358418001 205479260072689526518813501)
    ·
      refine ⟨77054722527258572444555063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205479260072689526518813501 77054722527258572444555063)
      ·
        refine ⟨115582083790887858666832595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77054722527258572444555063 115582083790887858666832595)
        ·
          refine ⟨173373125686331788000248893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115582083790887858666832595 173373125686331788000248893)
          ·
            refine ⟨65014922132374420500093335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173373125686331788000248893 65014922132374420500093335)
            ·
              refine ⟨97522383198561630750140003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65014922132374420500093335 97522383198561630750140003)
              ·
                refine ⟨146283574797842446125210005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97522383198561630750140003 146283574797842446125210005)
                ·
                  refine ⟨6857042568648864662119219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146283574797842446125210005 6857042568648864662119219)
                  ·
                    refine ⟨10285563852973296993178829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6857042568648864662119219 10285563852973296993178829)
                    ·
                      refine ⟨3857086444864986372442061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285563852973296993178829 3857086444864986372442061)
                      ·
                        rfl

theorem cell23_7511649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_7511649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511649 prefixEnd_7511649 := by exact prefixLift 7511649
  have htrace : WordTrace (prefixWord ++ tailWord_7511649) baseStart_7511649 baseEnd_7511649 := by
    simpa [prefixWord, tailWord_7511649, baseEnd_7511649] using wordTrace_append hprefix tailTrace_7511649
  have hstable : (prefixWord ++ tailWord_7511649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511649).length < 2 ^ (prefixWord ++ tailWord_7511649).sum := by decide
  have hdescent : baseEnd_7511649 < baseStart_7511649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511666 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_7511666 : Nat := 118140960795 + 7511666 * 2 ^ 59
def prefixEnd_7511666 : Nat := 4983230072969 + 3 ^ 40 * 7511666 * 2
def baseEnd_7511666 : Nat := 3857095174036112805929483

theorem tailTrace_7511666 : CollatzResearch.WordTrace tailWord_7511666 prefixEnd_7511666 3857095174036112805929483 := by
  unfold tailWord_7511666
  simp only [CollatzResearch.WordTrace]
  refine ⟨68493241701131111815446713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182648644536349631507857901 68493241701131111815446713)
  ·
    refine ⟨51369931275848333861585035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68493241701131111815446713 51369931275848333861585035)
    ·
      refine ⟨77054896913772500792377553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51369931275848333861585035 77054896913772500792377553)
      ·
        refine ⟨57791172685329375594283165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77054896913772500792377553 57791172685329375594283165)
        ·
          refine ⟨21671689756998515847856187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57791172685329375594283165 21671689756998515847856187)
          ·
            refine ⟨32507534635497773771784281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21671689756998515847856187 32507534635497773771784281)
            ·
              refine ⟨24380650976623330328838211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32507534635497773771784281 24380650976623330328838211)
              ·
                refine ⟨36570976464934995493257317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24380650976623330328838211 36570976464934995493257317)
                ·
                  refine ⟨6857058087175311654985747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36570976464934995493257317 6857058087175311654985747)
                  ·
                    refine ⟨10285587130762967482478621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6857058087175311654985747 10285587130762967482478621)
                    ·
                      refine ⟨3857095174036112805929483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285587130762967482478621 3857095174036112805929483)
                      ·
                        rfl

theorem cell23_7511666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_7511666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511666 prefixEnd_7511666 := by exact prefixLift 7511666
  have htrace : WordTrace (prefixWord ++ tailWord_7511666) baseStart_7511666 baseEnd_7511666 := by
    simpa [prefixWord, tailWord_7511666, baseEnd_7511666] using wordTrace_append hprefix tailTrace_7511666
  have hstable : (prefixWord ++ tailWord_7511666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511666).length < 2 ^ (prefixWord ++ tailWord_7511666).sum := by decide
  have hdescent : baseEnd_7511666 < baseStart_7511666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511692 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_7511692 : Nat := 118140960795 + 7511692 * 2 ^ 59
def prefixEnd_7511692 : Nat := 4983230072969 + 3 ^ 40 * 7511692 * 2
def baseEnd_7511692 : Nat := 3857108524533129704204363

theorem tailTrace_7511692 : CollatzResearch.WordTrace tailWord_7511692 prefixEnd_7511692 3857108524533129704204363 := by
  unfold tailWord_7511692
  simp only [CollatzResearch.WordTrace]
  refine ⟨136986957551215126851116665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182649276734953502468155553 136986957551215126851116665)
  ·
    refine ⟨102740218163411345138337499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136986957551215126851116665 102740218163411345138337499)
    ·
      refine ⟨154110327245117017707506249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102740218163411345138337499 154110327245117017707506249)
      ·
        refine ⟨115582745433837763280629687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154110327245117017707506249 115582745433837763280629687)
        ·
          refine ⟨173374118150756644920944531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115582745433837763280629687 173374118150756644920944531)
          ·
            refine ⟨260061177226134967381416797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173374118150756644920944531 260061177226134967381416797)
            ·
              refine ⟨97522941459800612768031299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260061177226134967381416797 97522941459800612768031299)
              ·
                refine ⟨146284412189700919152046949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97522941459800612768031299 146284412189700919152046949)
                ·
                  refine ⟨27428327285568922341008803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146284412189700919152046949 27428327285568922341008803)
                  ·
                    refine ⟨41142490928353383511513205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27428327285568922341008803 41142490928353383511513205)
                    ·
                      refine ⟨3857108524533129704204363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41142490928353383511513205 3857108524533129704204363)
                      ·
                        rfl

theorem cell23_7511692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_7511692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511692 prefixEnd_7511692 := by exact prefixLift 7511692
  have htrace : WordTrace (prefixWord ++ tailWord_7511692) baseStart_7511692 baseEnd_7511692 := by
    simpa [prefixWord, tailWord_7511692, baseEnd_7511692] using wordTrace_append hprefix tailTrace_7511692
  have hstable : (prefixWord ++ tailWord_7511692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511692).length < 2 ^ (prefixWord ++ tailWord_7511692).sum := by decide
  have hdescent : baseEnd_7511692 < baseStart_7511692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511799 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_7511799 : Nat := 118140960795 + 7511799 * 2 ^ 59
def prefixEnd_7511799 : Nat := 4983230072969 + 3 ^ 40 * 7511799 * 2
def baseEnd_7511799 : Nat := 3857163466963160785566371

theorem tailTrace_7511799 : CollatzResearch.WordTrace tailWord_7511799 prefixEnd_7511799 3857163466963160785566371 := by
  unfold tailWord_7511799
  simp only [CollatzResearch.WordTrace]
  refine ⟨273977817713042610976378451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182651878475361740650918967 273977817713042610976378451)
  ·
    refine ⟨410966726569563916464567677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273977817713042610976378451 410966726569563916464567677)
    ·
      refine ⟨154112522463586468674212879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410966726569563916464567677 154112522463586468674212879)
      ·
        refine ⟨231168783695379703011319319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154112522463586468674212879 231168783695379703011319319)
        ·
          refine ⟨346753175543069554516978979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231168783695379703011319319 346753175543069554516978979)
          ·
            refine ⟨520129763314604331775468469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346753175543069554516978979 520129763314604331775468469)
            ·
              refine ⟨48762165310744156103950169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 520129763314604331775468469 48762165310744156103950169)
              ·
                refine ⟨36571623983058117077962627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48762165310744156103950169 36571623983058117077962627)
                ·
                  refine ⟨54857435974587175616943941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36571623983058117077962627 54857435974587175616943941)
                  ·
                    refine ⟨10285769245235095428176989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54857435974587175616943941 10285769245235095428176989)
                    ·
                      refine ⟨3857163466963160785566371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285769245235095428176989 3857163466963160785566371)
                      ·
                        rfl

theorem cell23_7511799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_7511799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511799 prefixEnd_7511799 := by exact prefixLift 7511799
  have htrace : WordTrace (prefixWord ++ tailWord_7511799) baseStart_7511799 baseEnd_7511799 := by
    simpa [prefixWord, tailWord_7511799, baseEnd_7511799] using wordTrace_append hprefix tailTrace_7511799
  have hstable : (prefixWord ++ tailWord_7511799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511799).length < 2 ^ (prefixWord ++ tailWord_7511799).sum := by decide
  have hdescent : baseEnd_7511799 < baseStart_7511799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511816 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_7511816 : Nat := 118140960795 + 7511816 * 2 ^ 59
def prefixEnd_7511816 : Nat := 4983230072969 + 3 ^ 40 * 7511816 * 2
def baseEnd_7511816 : Nat := 3857172196134287219053793

theorem tailTrace_7511816 : CollatzResearch.WordTrace tailWord_7511816 prefixEnd_7511816 3857172196134287219053793 := by
  unfold tailWord_7511816
  simp only [CollatzResearch.WordTrace]
  refine ⟨136989218876990511439873651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182652291835987348586498201 136989218876990511439873651)
  ·
    refine ⟨205483828315485767159810477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136989218876990511439873651 205483828315485767159810477)
    ·
      refine ⟨77056435618307162684928929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205483828315485767159810477 77056435618307162684928929)
      ·
        refine ⟨57792326713730372013696697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77056435618307162684928929 57792326713730372013696697)
        ·
          refine ⟨43344245035297779010272523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57792326713730372013696697 43344245035297779010272523)
          ·
            refine ⟨65016367552946668515408785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43344245035297779010272523 65016367552946668515408785)
            ·
              refine ⟨48762275664710001386556589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65016367552946668515408785 48762275664710001386556589)
              ·
                refine ⟨18285853374266250519958721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48762275664710001386556589 18285853374266250519958721)
                ·
                  refine ⟨13714390030699687889969041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18285853374266250519958721 13714390030699687889969041)
                  ·
                    refine ⟨10285792523024765917476781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13714390030699687889969041 10285792523024765917476781)
                    ·
                      refine ⟨3857172196134287219053793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285792523024765917476781 3857172196134287219053793)
                      ·
                        rfl

theorem cell23_7511816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_7511816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511816 prefixEnd_7511816 := by exact prefixLift 7511816
  have htrace : WordTrace (prefixWord ++ tailWord_7511816) baseStart_7511816 baseEnd_7511816 := by
    simpa [prefixWord, tailWord_7511816, baseEnd_7511816] using wordTrace_append hprefix tailTrace_7511816
  have hstable : (prefixWord ++ tailWord_7511816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511816).length < 2 ^ (prefixWord ++ tailWord_7511816).sum := by decide
  have hdescent : baseEnd_7511816 < baseStart_7511816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511840 : List Nat := [2, 1, 1, 5, 1, 1, 5, 2, 1, 4]
def baseStart_7511840 : Nat := 118140960795 + 7511840 * 2 ^ 59
def prefixEnd_7511840 : Nat := 4983230072969 + 3 ^ 40 * 7511840 * 2
def baseEnd_7511840 : Nat := 1285728173223331708384561

theorem tailTrace_7511840 : CollatzResearch.WordTrace tailWord_7511840 prefixEnd_7511840 1285728173223331708384561 := by
  unfold tailWord_7511840
  simp only [CollatzResearch.WordTrace]
  refine ⟨136989656552947037489310487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182652875403929383319080649 136989656552947037489310487)
  ·
    refine ⟨205484484829420556233965731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136989656552947037489310487 205484484829420556233965731)
    ·
      refine ⟨308226727244130834350948597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205484484829420556233965731 308226727244130834350948597)
      ·
        refine ⟨28896255679137265720401431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308226727244130834350948597 28896255679137265720401431)
        ·
          refine ⟨43344383518705898580602147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28896255679137265720401431 43344383518705898580602147)
          ·
            refine ⟨65016575278058847870903221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43344383518705898580602147 65016575278058847870903221)
            ·
              refine ⟨6095303932318016987897177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65016575278058847870903221 6095303932318016987897177)
              ·
                refine ⟨4571477949238512740922883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6095303932318016987897177 4571477949238512740922883)
                ·
                  refine ⟨6857216923857769111384325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571477949238512740922883 6857216923857769111384325)
                  ·
                    refine ⟨1285728173223331708384561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6857216923857769111384325 1285728173223331708384561)
                    ·
                      rfl

theorem cell23_7511840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 4].length) (baseStart_7511840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511840 prefixEnd_7511840 := by exact prefixLift 7511840
  have htrace : WordTrace (prefixWord ++ tailWord_7511840) baseStart_7511840 baseEnd_7511840 := by
    simpa [prefixWord, tailWord_7511840, baseEnd_7511840] using wordTrace_append hprefix tailTrace_7511840
  have hstable : (prefixWord ++ tailWord_7511840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511840).length < 2 ^ (prefixWord ++ tailWord_7511840).sum := by decide
  have hdescent : baseEnd_7511840 < baseStart_7511840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511866 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_7511866 : Nat := 118140960795 + 7511866 * 2 ^ 59
def prefixEnd_7511866 : Nat := 4983230072969 + 3 ^ 40 * 7511866 * 2
def baseEnd_7511866 : Nat := 1285732623389004007809521

theorem tailTrace_7511866 : CollatzResearch.WordTrace tailWord_7511866 prefixEnd_7511866 1285732623389004007809521 := by
  unfold tailWord_7511866
  simp only [CollatzResearch.WordTrace]
  refine ⟨68495065350949970354766863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182653507602533254279378301 68495065350949970354766863)
  ·
    refine ⟨102742598026424955532150295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68495065350949970354766863 102742598026424955532150295)
    ·
      refine ⟨154113897039637433298225443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102742598026424955532150295 154113897039637433298225443)
      ·
        refine ⟨231170845559456149947338165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154113897039637433298225443 231170845559456149947338165)
        ·
          refine ⟨21672266771199014057562953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231170845559456149947338165 21672266771199014057562953)
          ·
            refine ⟨16254200078399260543172215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21672266771199014057562953 16254200078399260543172215)
            ·
              refine ⟨24381300117598890814758323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16254200078399260543172215 24381300117598890814758323)
              ·
                refine ⟨36571950176398336222137485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24381300117598890814758323 36571950176398336222137485)
                ·
                  refine ⟨13714481316149376083301557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36571950176398336222137485 13714481316149376083301557)
                  ·
                    refine ⟨1285732623389004007809521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13714481316149376083301557 1285732623389004007809521)
                    ·
                      rfl

theorem cell23_7511866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_7511866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511866 prefixEnd_7511866 := by exact prefixLift 7511866
  have htrace : WordTrace (prefixWord ++ tailWord_7511866) baseStart_7511866 baseEnd_7511866 := by
    simpa [prefixWord, tailWord_7511866, baseEnd_7511866] using wordTrace_append hprefix tailTrace_7511866
  have hstable : (prefixWord ++ tailWord_7511866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511866).length < 2 ^ (prefixWord ++ tailWord_7511866).sum := by decide
  have hdescent : baseEnd_7511866 < baseStart_7511866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511879 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 3, 6]
def baseStart_7511879 : Nat := 118140960795 + 7511879 * 2 ^ 59
def prefixEnd_7511879 : Nat := 4983230072969 + 3 ^ 40 * 7511879 * 2
def baseEnd_7511879 : Nat := 1285734848471840157522001

theorem tailTrace_7511879 : CollatzResearch.WordTrace tailWord_7511879 prefixEnd_7511879 1285734848471840157522001 := by
  unfold tailWord_7511879
  simp only [CollatzResearch.WordTrace]
  refine ⟨273980735552752784639290691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182653823701835189759527127 273980735552752784639290691)
  ·
    refine ⟨410971103329129176958936037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273980735552752784639290691 410971103329129176958936037)
    ·
      refine ⟨77057081874211720679800507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 410971103329129176958936037 77057081874211720679800507)
      ·
        refine ⟨115585622811317581019700761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77057081874211720679800507 115585622811317581019700761)
        ·
          refine ⟨86689217108488185764775571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115585622811317581019700761 86689217108488185764775571)
          ·
            refine ⟨130033825662732278647163357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86689217108488185764775571 130033825662732278647163357)
            ·
              refine ⟨48762684623524604492686259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130033825662732278647163357 48762684623524604492686259)
              ·
                refine ⟨73144026935286906739029389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48762684623524604492686259 73144026935286906739029389)
                ·
                  refine ⟨27429010100732590027136021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73144026935286906739029389 27429010100732590027136021)
                  ·
                    refine ⟨1285734848471840157522001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27429010100732590027136021 1285734848471840157522001)
                    ·
                      rfl

theorem cell23_7511879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_7511879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511879 prefixEnd_7511879 := by exact prefixLift 7511879
  have htrace : WordTrace (prefixWord ++ tailWord_7511879) baseStart_7511879 baseEnd_7511879 := by
    simpa [prefixWord, tailWord_7511879, baseEnd_7511879] using wordTrace_append hprefix tailTrace_7511879
  have hstable : (prefixWord ++ tailWord_7511879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511879).length < 2 ^ (prefixWord ++ tailWord_7511879).sum := by decide
  have hdescent : baseEnd_7511879 < baseStart_7511879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511916 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_7511916 : Nat := 118140960795 + 7511916 * 2 ^ 59
def prefixEnd_7511916 : Nat := 4983230072969 + 3 ^ 40 * 7511916 * 2
def baseEnd_7511916 : Nat := 3857223544199736827803333

theorem tailTrace_7511916 : CollatzResearch.WordTrace tailWord_7511916 prefixEnd_7511916 3857223544199736827803333 := by
  unfold tailWord_7511916
  simp only [CollatzResearch.WordTrace]
  refine ⟨136991042526809369979193801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182654723369079159972258401 136991042526809369979193801)
  ·
    refine ⟨102743281895107027484395351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136991042526809369979193801 102743281895107027484395351)
    ·
      refine ⟨154114922842660541226593027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102743281895107027484395351 154114922842660541226593027)
      ·
        refine ⟨231172384263990811839889541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154114922842660541226593027 231172384263990811839889541)
        ·
          refine ⟨43344822049498277219979289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231172384263990811839889541 43344822049498277219979289)
          ·
            refine ⟨32508616537123707914984467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43344822049498277219979289 32508616537123707914984467)
            ·
              refine ⟨48762924805685561872476701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32508616537123707914984467 48762924805685561872476701)
              ·
                refine ⟨18286096802132085702178763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48762924805685561872476701 18286096802132085702178763)
                ·
                  refine ⟨27429145203198128553268145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18286096802132085702178763 27429145203198128553268145)
                  ·
                    refine ⟨20571858902398596414951109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27429145203198128553268145 20571858902398596414951109)
                    ·
                      refine ⟨3857223544199736827803333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20571858902398596414951109 3857223544199736827803333)
                      ·
                        rfl

theorem cell23_7511916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_7511916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511916 prefixEnd_7511916 := by exact prefixLift 7511916
  have htrace : WordTrace (prefixWord ++ tailWord_7511916) baseStart_7511916 baseEnd_7511916 := by
    simpa [prefixWord, tailWord_7511916, baseEnd_7511916] using wordTrace_append hprefix tailTrace_7511916
  have hstable : (prefixWord ++ tailWord_7511916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511916).length < 2 ^ (prefixWord ++ tailWord_7511916).sum := by decide
  have hdescent : baseEnd_7511916 < baseStart_7511916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511936 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 3]
def baseStart_7511936 : Nat := 118140960795 + 7511936 * 2 ^ 59
def prefixEnd_7511936 : Nat := 4983230072969 + 3 ^ 40 * 7511936 * 2
def baseEnd_7511936 : Nat := 3857233813812826749553241

theorem tailTrace_7511936 : CollatzResearch.WordTrace tailWord_7511936 prefixEnd_7511936 3857233813812826749553241 := by
  unfold tailWord_7511936
  simp only [CollatzResearch.WordTrace]
  refine ⟨136991407256773141687057831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182655209675697522249410441 136991407256773141687057831)
  ·
    refine ⟨205487110885159712530586747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136991407256773141687057831 205487110885159712530586747)
    ·
      refine ⟨308230666327739568795880121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205487110885159712530586747 308230666327739568795880121)
      ·
        refine ⟨231172999745804676596910091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308230666327739568795880121 231172999745804676596910091)
        ·
          refine ⟨346759499618707014895365137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231172999745804676596910091 346759499618707014895365137)
          ·
            refine ⟨260069624714030261171523853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346759499618707014895365137 260069624714030261171523853)
            ·
              refine ⟨97526109267761347939321445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260069624714030261171523853 97526109267761347939321445)
              ·
                refine ⟨18286145487705252738622771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97526109267761347939321445 18286145487705252738622771)
                ·
                  refine ⟨27429218231557879107934157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18286145487705252738622771 27429218231557879107934157)
                  ·
                    refine ⟨10285956836834204665475309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27429218231557879107934157 10285956836834204665475309)
                    ·
                      refine ⟨3857233813812826749553241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285956836834204665475309 3857233813812826749553241)
                      ·
                        rfl

theorem cell23_7511936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_7511936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511936 prefixEnd_7511936 := by exact prefixLift 7511936
  have htrace : WordTrace (prefixWord ++ tailWord_7511936) baseStart_7511936 baseEnd_7511936 := by
    simpa [prefixWord, tailWord_7511936, baseEnd_7511936] using wordTrace_append hprefix tailTrace_7511936
  have hstable : (prefixWord ++ tailWord_7511936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511936).length < 2 ^ (prefixWord ++ tailWord_7511936).sum := by decide
  have hdescent : baseEnd_7511936 < baseStart_7511936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511940 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_7511940 : Nat := 118140960795 + 7511940 * 2 ^ 59
def prefixEnd_7511940 : Nat := 4983230072969 + 3 ^ 40 * 7511940 * 2
def baseEnd_7511940 : Nat := 3857235867735444733903223

theorem tailTrace_7511940 : CollatzResearch.WordTrace tailWord_7511940 prefixEnd_7511940 3857235867735444733903223 := by
  unfold tailWord_7511940
  simp only [CollatzResearch.WordTrace]
  refine ⟨136991480202765896028630637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182655306937021194704840849 136991480202765896028630637)
  ·
    refine ⟨51371805076037211010736489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136991480202765896028630637 51371805076037211010736489)
    ·
      refine ⟨38528853807027908258052367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51371805076037211010736489 38528853807027908258052367)
      ·
        refine ⟨57793280710541862387078551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38528853807027908258052367 57793280710541862387078551)
        ·
          refine ⟨86689921065812793580617827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57793280710541862387078551 86689921065812793580617827)
          ·
            refine ⟨130034881598719190370926741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86689921065812793580617827 130034881598719190370926741)
            ·
              refine ⟨6095385074939962048637191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130034881598719190370926741 6095385074939962048637191)
              ·
                refine ⟨9143077612409943072955787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095385074939962048637191 9143077612409943072955787)
                ·
                  refine ⟨13714616418614914609433681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9143077612409943072955787 13714616418614914609433681)
                  ·
                    refine ⟨10285962313961185957075261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13714616418614914609433681 10285962313961185957075261)
                    ·
                      refine ⟨3857235867735444733903223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10285962313961185957075261 3857235867735444733903223)
                      ·
                        rfl

theorem cell23_7511940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_7511940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511940 prefixEnd_7511940 := by exact prefixLift 7511940
  have htrace : WordTrace (prefixWord ++ tailWord_7511940) baseStart_7511940 baseEnd_7511940 := by
    simpa [prefixWord, tailWord_7511940, baseEnd_7511940] using wordTrace_append hprefix tailTrace_7511940
  have hstable : (prefixWord ++ tailWord_7511940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511940).length < 2 ^ (prefixWord ++ tailWord_7511940).sum := by decide
  have hdescent : baseEnd_7511940 < baseStart_7511940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511954 : List Nat := [3, 2, 3, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_7511954 : Nat := 118140960795 + 7511954 * 2 ^ 59
def prefixEnd_7511954 : Nat := 4983230072969 + 3 ^ 40 * 7511954 * 2
def baseEnd_7511954 : Nat := 3857243056464607679128159

theorem tailTrace_7511954 : CollatzResearch.WordTrace tailWord_7511954 prefixEnd_7511954 3857243056464607679128159 := by
  unfold tailWord_7511954
  simp only [CollatzResearch.WordTrace]
  refine ⟨68495867756870268112067729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182655647351654048298847277 68495867756870268112067729)
  ·
    refine ⟨51371900817652701084050797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68495867756870268112067729 51371900817652701084050797)
    ·
      refine ⟨19264462806619762906519049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51371900817652701084050797 19264462806619762906519049)
      ·
        refine ⟨14448347104964822179889287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19264462806619762906519049 14448347104964822179889287)
        ·
          refine ⟨21672520657447233269833931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14448347104964822179889287 21672520657447233269833931)
          ·
            refine ⟨32508780986170849904750897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21672520657447233269833931 32508780986170849904750897)
            ·
              refine ⟨24381585739628137428563173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32508780986170849904750897 24381585739628137428563173)
              ·
                refine ⟨4571547326180275767855595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24381585739628137428563173 4571547326180275767855595)
                ·
                  refine ⟨6857320989270413651783393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571547326180275767855595 6857320989270413651783393)
                  ·
                    refine ⟨5142990741952810238837545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6857320989270413651783393 5142990741952810238837545)
                    ·
                      refine ⟨3857243056464607679128159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5142990741952810238837545 3857243056464607679128159)
                      ·
                        rfl

theorem cell23_7511954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_7511954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511954 prefixEnd_7511954 := by exact prefixLift 7511954
  have htrace : WordTrace (prefixWord ++ tailWord_7511954) baseStart_7511954 baseEnd_7511954 := by
    simpa [prefixWord, tailWord_7511954, baseEnd_7511954] using wordTrace_append hprefix tailTrace_7511954
  have hstable : (prefixWord ++ tailWord_7511954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511954).length < 2 ^ (prefixWord ++ tailWord_7511954).sum := by decide
  have hdescent : baseEnd_7511954 < baseStart_7511954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511988 : List Nat := [2, 5, 2, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_7511988 : Nat := 118140960795 + 7511988 * 2 ^ 59
def prefixEnd_7511988 : Nat := 4983230072969 + 3 ^ 40 * 7511988 * 2
def baseEnd_7511988 : Nat := 3857260514806860546103003

theorem tailTrace_7511988 : CollatzResearch.WordTrace tailWord_7511988 prefixEnd_7511988 3857260514806860546103003 := by
  unfold tailWord_7511988
  simp only [CollatzResearch.WordTrace]
  refine ⟨136992355554678948127504309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182656474072905264170005745 136992355554678948127504309)
  ·
    refine ⟨12843033333251151386953529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136992355554678948127504309 12843033333251151386953529)
    ·
      refine ⟨9632274999938363540215147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12843033333251151386953529 9632274999938363540215147)
      ·
        refine ⟨14448412499907545310322721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9632274999938363540215147 14448412499907545310322721)
        ·
          refine ⟨10836309374930658982742041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14448412499907545310322721 10836309374930658982742041)
          ·
            refine ⟨8127232031197994237056531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10836309374930658982742041 8127232031197994237056531)
            ·
              refine ⟨12190848046796991355584797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8127232031197994237056531 12190848046796991355584797)
              ·
                refine ⟨4571568017548871758344299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12190848046796991355584797 4571568017548871758344299)
                ·
                  refine ⟨6857352026323307637516449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571568017548871758344299 6857352026323307637516449)
                  ·
                    refine ⟨5143014019742480728137337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6857352026323307637516449 5143014019742480728137337)
                    ·
                      refine ⟨3857260514806860546103003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143014019742480728137337 3857260514806860546103003)
                      ·
                        rfl

theorem cell23_7511988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_7511988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511988 prefixEnd_7511988 := by exact prefixLift 7511988
  have htrace : WordTrace (prefixWord ++ tailWord_7511988) baseStart_7511988 baseEnd_7511988 := by
    simpa [prefixWord, tailWord_7511988, baseEnd_7511988] using wordTrace_append hprefix tailTrace_7511988
  have hstable : (prefixWord ++ tailWord_7511988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511988).length < 2 ^ (prefixWord ++ tailWord_7511988).sum := by decide
  have hdescent : baseEnd_7511988 < baseStart_7511988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7511993 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 3, 4, 2]
def baseStart_7511993 : Nat := 118140960795 + 7511993 * 2 ^ 59
def prefixEnd_7511993 : Nat := 4983230072969 + 3 ^ 40 * 7511993 * 2
def baseEnd_7511993 : Nat := 3857263082210133026540479

theorem tailTrace_7511993 : CollatzResearch.WordTrace tailWord_7511993 prefixEnd_7511993 3857263082210133026540479 := by
  unfold tailWord_7511993
  simp only [CollatzResearch.WordTrace]
  refine ⟨273984893474339782108940633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182656595649559854739293755 273984893474339782108940633)
  ·
    refine ⟨205488670105754836581705475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273984893474339782108940633 205488670105754836581705475)
    ·
      refine ⟨308233005158632254872558213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205488670105754836581705475 308233005158632254872558213)
      ·
        refine ⟨57793688467243547788604665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308233005158632254872558213 57793688467243547788604665)
        ·
          refine ⟨43345266350432660841453499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57793688467243547788604665 43345266350432660841453499)
          ·
            refine ⟨65017899525648991262180249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43345266350432660841453499 65017899525648991262180249)
            ·
              refine ⟨48763424644236743446635187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65017899525648991262180249 48763424644236743446635187)
              ·
                refine ⟨73145136966355115169952781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48763424644236743446635187 73145136966355115169952781)
                ·
                  refine ⟨27429426362383168188732293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73145136966355115169952781 27429426362383168188732293)
                  ·
                    refine ⟨5143017442946844035387305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27429426362383168188732293 5143017442946844035387305)
                    ·
                      refine ⟨3857263082210133026540479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143017442946844035387305 3857263082210133026540479)
                      ·
                        rfl

theorem cell23_7511993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_7511993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7511993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7511993 prefixEnd_7511993 := by exact prefixLift 7511993
  have htrace : WordTrace (prefixWord ++ tailWord_7511993) baseStart_7511993 baseEnd_7511993 := by
    simpa [prefixWord, tailWord_7511993, baseEnd_7511993] using wordTrace_append hprefix tailTrace_7511993
  have hstable : (prefixWord ++ tailWord_7511993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7511993).length < 2 ^ (prefixWord ++ tailWord_7511993).sum := by decide
  have hdescent : baseEnd_7511993 < baseStart_7511993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7511993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512010 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_7512010 : Nat := 118140960795 + 7512010 * 2 ^ 59
def prefixEnd_7512010 : Nat := 4983230072969 + 3 ^ 40 * 7512010 * 2
def baseEnd_7512010 : Nat := 3857271811381259460027901

theorem tailTrace_7512010 : CollatzResearch.WordTrace tailWord_7512010 prefixEnd_7512010 3857271811381259460027901 := by
  unfold tailWord_7512010
  simp only [CollatzResearch.WordTrace]
  refine ⟨68496378378819548503077371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182657009010185462674872989 68496378378819548503077371)
  ·
    refine ⟨102744567568229322754616057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68496378378819548503077371 102744567568229322754616057)
    ·
      refine ⟨77058425676171992065962043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102744567568229322754616057 77058425676171992065962043)
      ·
        refine ⟨115587638514257988098943065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77058425676171992065962043 115587638514257988098943065)
        ·
          refine ⟨86690728885693491074207299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115587638514257988098943065 86690728885693491074207299)
          ·
            refine ⟨130036093328540236611310949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86690728885693491074207299 130036093328540236611310949)
            ·
              refine ⟨24381767499101294364620803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130036093328540236611310949 24381767499101294364620803)
              ·
                refine ⟨36572651248651941546931205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24381767499101294364620803 36572651248651941546931205)
                ·
                  refine ⟨6857372109122239040049601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36572651248651941546931205 6857372109122239040049601)
                  ·
                    refine ⟨5143029081841679280037201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6857372109122239040049601 5143029081841679280037201)
                    ·
                      refine ⟨3857271811381259460027901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143029081841679280037201 3857271811381259460027901)
                      ·
                        rfl

theorem cell23_7512010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_7512010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512010 prefixEnd_7512010 := by exact prefixLift 7512010
  have htrace : WordTrace (prefixWord ++ tailWord_7512010) baseStart_7512010 baseEnd_7512010 := by
    simpa [prefixWord, tailWord_7512010, baseEnd_7512010] using wordTrace_append hprefix tailTrace_7512010
  have hstable : (prefixWord ++ tailWord_7512010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512010).length < 2 ^ (prefixWord ++ tailWord_7512010).sum := by decide
  have hdescent : baseEnd_7512010 < baseStart_7512010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512016 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 7]
def baseStart_7512016 : Nat := 118140960795 + 7512016 * 2 ^ 59
def prefixEnd_7512016 : Nat := 4983230072969 + 3 ^ 40 * 7512016 * 2
def baseEnd_7512016 : Nat := 428586099140576270728097

theorem tailTrace_7512016 : CollatzResearch.WordTrace tailWord_7512016 prefixEnd_7512016 428586099140576270728097 := by
  unfold tailWord_7512016
  simp only [CollatzResearch.WordTrace]
  refine ⟨136992866176628228518513951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182657154902170971358018601 136992866176628228518513951)
  ·
    refine ⟨205489299264942342777770927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136992866176628228518513951 205489299264942342777770927)
    ·
      refine ⟨308233948897413514166656391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205489299264942342777770927 308233948897413514166656391)
      ·
        refine ⟨462350923346120271249984587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308233948897413514166656391 462350923346120271249984587)
        ·
          refine ⟨693526385019180406874976881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462350923346120271249984587 693526385019180406874976881)
          ·
            refine ⟨520144788764385305156232661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693526385019180406874976881 520144788764385305156232661)
            ·
              refine ⟨12190893486665280589599203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 520144788764385305156232661 12190893486665280589599203)
              ·
                refine ⟨18286340229997920884398805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12190893486665280589599203 18286340229997920884398805)
                ·
                  refine ⟨428586099140576270728097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18286340229997920884398805 428586099140576270728097)
                  ·
                    rfl

theorem cell23_7512016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 7].length) (baseStart_7512016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512016 prefixEnd_7512016 := by exact prefixLift 7512016
  have htrace : WordTrace (prefixWord ++ tailWord_7512016) baseStart_7512016 baseEnd_7512016 := by
    simpa [prefixWord, tailWord_7512016, baseEnd_7512016] using wordTrace_append hprefix tailTrace_7512016
  have hstable : (prefixWord ++ tailWord_7512016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512016).length < 2 ^ (prefixWord ++ tailWord_7512016).sum := by decide
  have hdescent : baseEnd_7512016 < baseStart_7512016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512056 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_7512056 : Nat := 118140960795 + 7512056 * 2 ^ 59
def prefixEnd_7512056 : Nat := 4983230072969 + 3 ^ 40 * 7512056 * 2
def baseEnd_7512056 : Nat := 3857295431491366280052689

theorem tailTrace_7512056 : CollatzResearch.WordTrace tailWord_7512056 prefixEnd_7512056 3857295431491366280052689 := by
  unfold tailWord_7512056
  simp only [CollatzResearch.WordTrace]
  refine ⟨136993595636555771934242011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182658127515407695912322681 136993595636555771934242011)
  ·
    refine ⟨205490393454833657901363017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136993595636555771934242011 205490393454833657901363017)
    ·
      refine ⟨154117795091125243426022263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205490393454833657901363017 154117795091125243426022263)
      ·
        refine ⟨231176692636687865139033395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154117795091125243426022263 231176692636687865139033395)
        ·
          refine ⟨346765038955031797708550093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231176692636687865139033395 346765038955031797708550093)
          ·
            refine ⟨130036889608136924140706285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346765038955031797708550093 130036889608136924140706285)
            ·
              refine ⟨48763833603051346552764857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130036889608136924140706285 48763833603051346552764857)
              ·
                refine ⟨36572875202288509914573643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48763833603051346552764857 36572875202288509914573643)
                ·
                  refine ⟨54859312803432764871860465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36572875202288509914573643 54859312803432764871860465)
                  ·
                    refine ⟨41144484602574573653895349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54859312803432764871860465 41144484602574573653895349)
                    ·
                      refine ⟨3857295431491366280052689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41144484602574573653895349 3857295431491366280052689)
                      ·
                        rfl

theorem cell23_7512056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_7512056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512056 prefixEnd_7512056 := by exact prefixLift 7512056
  have htrace : WordTrace (prefixWord ++ tailWord_7512056) baseStart_7512056 baseEnd_7512056 := by
    simpa [prefixWord, tailWord_7512056, baseEnd_7512056] using wordTrace_append hprefix tailTrace_7512056
  have hstable : (prefixWord ++ tailWord_7512056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512056).length < 2 ^ (prefixWord ++ tailWord_7512056).sum := by decide
  have hdescent : baseEnd_7512056 < baseStart_7512056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512083 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 1, 6, 2]
def baseStart_7512083 : Nat := 118140960795 + 7512083 * 2 ^ 59
def prefixEnd_7512083 : Nat := 4983230072969 + 3 ^ 40 * 7512083 * 2
def baseEnd_7512083 : Nat := 3857309295469037674415065

theorem tailTrace_7512083 : CollatzResearch.WordTrace tailWord_7512083 prefixEnd_7512083 3857309295469037674415065 := by
  unfold tailWord_7512083
  simp only [CollatzResearch.WordTrace]
  refine ⟨273988176044013727479716903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182658784029342484986477935 273988176044013727479716903)
  ·
    refine ⟨410982264066020591219575355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273988176044013727479716903 410982264066020591219575355)
    ·
      refine ⟨616473396099030886829363033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410982264066020591219575355 616473396099030886829363033)
      ·
        refine ⟨462355047074273165122022275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616473396099030886829363033 462355047074273165122022275)
        ·
          refine ⟨693532570611409747683033413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462355047074273165122022275 693532570611409747683033413)
          ·
            refine ⟨130037356989639327690568765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 693532570611409747683033413 130037356989639327690568765)
            ·
              refine ⟨48764008871114747883963287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130037356989639327690568765 48764008871114747883963287)
              ·
                refine ⟨73146013306672121825944931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48764008871114747883963287 73146013306672121825944931)
                ·
                  refine ⟨109719019960008182738917397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73146013306672121825944931 109719019960008182738917397)
                  ·
                    refine ⟨5143079060625383565886753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109719019960008182738917397 5143079060625383565886753)
                    ·
                      refine ⟨3857309295469037674415065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143079060625383565886753 3857309295469037674415065)
                      ·
                        rfl

theorem cell23_7512083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 6, 2].length) (baseStart_7512083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512083 prefixEnd_7512083 := by exact prefixLift 7512083
  have htrace : WordTrace (prefixWord ++ tailWord_7512083) baseStart_7512083 baseEnd_7512083 := by
    simpa [prefixWord, tailWord_7512083, baseEnd_7512083] using wordTrace_append hprefix tailTrace_7512083
  have hstable : (prefixWord ++ tailWord_7512083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512083).length < 2 ^ (prefixWord ++ tailWord_7512083).sum := by decide
  have hdescent : baseEnd_7512083 < baseStart_7512083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
