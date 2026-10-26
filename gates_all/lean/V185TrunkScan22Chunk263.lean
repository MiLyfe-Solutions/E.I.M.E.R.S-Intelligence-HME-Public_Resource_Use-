import V185TrunkScan22Chunk262

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2346529 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2346529 : Nat := 118140960795 + 2346529 * 2 ^ 59
def prefixEnd_2346529 : Nat := 4983230072969 + 3 ^ 40 * 2346529 * 2
def baseEnd_2346529 : Nat := 803264831142769952130677

theorem tailTrace_2346529 : CollatzResearch.WordTrace tailWord_2346529 prefixEnd_2346529 803264831142769952130677 := by
  unfold tailWord_2346529
  simp only [CollatzResearch.WordTrace]
  refine ⟨85584943715933663092554641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57056629143955775395036427 85584943715933663092554641)
  ·
    refine ⟨64188707786950247319415981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85584943715933663092554641 64188707786950247319415981)
    ·
      refine ⟨24070765420106342744780993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64188707786950247319415981 24070765420106342744780993)
      ·
        refine ⟨18053074065079757058585745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24070765420106342744780993 18053074065079757058585745)
        ·
          refine ⟨13539805548809817793939309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18053074065079757058585745 13539805548809817793939309)
          ·
            refine ⟨5077427080803681672727241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13539805548809817793939309 5077427080803681672727241)
            ·
              refine ⟨3808070310602761254545431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5077427080803681672727241 3808070310602761254545431)
              ·
                refine ⟨5712105465904141881818147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808070310602761254545431 5712105465904141881818147)
                ·
                  refine ⟨8568158198856212822727221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5712105465904141881818147 8568158198856212822727221)
                  ·
                    refine ⟨803264831142769952130677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8568158198856212822727221 803264831142769952130677)
                    ·
                      rfl

theorem cell22_2346529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2346529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346529 prefixEnd_2346529 := by exact prefixLift 2346529
  have htrace : WordTrace (prefixWord ++ tailWord_2346529) baseStart_2346529 baseEnd_2346529 := by
    simpa [prefixWord, tailWord_2346529, baseEnd_2346529] using wordTrace_append hprefix tailTrace_2346529
  have hstable : (prefixWord ++ tailWord_2346529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346529).length < 2 ^ (prefixWord ++ tailWord_2346529).sum := by decide
  have hdescent : baseEnd_2346529 < baseStart_2346529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346550 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2346550 : Nat := 118140960795 + 2346550 * 2 ^ 59
def prefixEnd_2346550 : Nat := 4983230072969 + 3 ^ 40 * 2346550 * 2
def baseEnd_2346550 : Nat := 803272019871932897355613

theorem tailTrace_2346550 : CollatzResearch.WordTrace tailWord_2346550 prefixEnd_2346550 803272019871932897355613 := by
  unfold tailWord_2346550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5349106853053598979941819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57057139765905055786046069 5349106853053598979941819)
  ·
    refine ⟨8023660279580398469912729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5349106853053598979941819 8023660279580398469912729)
    ·
      refine ⟨6017745209685298852434547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8023660279580398469912729 6017745209685298852434547)
      ·
        refine ⟨9026617814527948278651821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6017745209685298852434547 9026617814527948278651821)
        ·
          refine ⟨3384981680447980604494433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9026617814527948278651821 3384981680447980604494433)
          ·
            refine ⟨2538736260335985453370825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3384981680447980604494433 2538736260335985453370825)
            ·
              refine ⟨1904052195251989090028119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2538736260335985453370825 1904052195251989090028119)
              ·
                refine ⟨2856078292877983635042179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904052195251989090028119 2856078292877983635042179)
                ·
                  refine ⟨4284117439316975452563269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856078292877983635042179 4284117439316975452563269)
                  ·
                    refine ⟨803272019871932897355613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4284117439316975452563269 803272019871932897355613)
                    ·
                      rfl

theorem cell22_2346550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2346550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346550 prefixEnd_2346550 := by exact prefixLift 2346550
  have htrace : WordTrace (prefixWord ++ tailWord_2346550) baseStart_2346550 baseEnd_2346550 := by
    simpa [prefixWord, tailWord_2346550, baseEnd_2346550] using wordTrace_append hprefix tailTrace_2346550
  have hstable : (prefixWord ++ tailWord_2346550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346550).length < 2 ^ (prefixWord ++ tailWord_2346550).sum := by decide
  have hdescent : baseEnd_2346550 < baseStart_2346550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346608 : List Nat := [2, 1, 1, 1, 6, 1, 3, 3, 1, 3]
def baseStart_2346608 : Nat := 118140960795 + 2346608 * 2 ^ 59
def prefixEnd_2346608 : Nat := 4983230072969 + 3 ^ 40 * 2346608 * 2
def baseEnd_2346608 : Nat := 803291874457240079405435

theorem tailTrace_2346608 : CollatzResearch.WordTrace tailWord_2346608 prefixEnd_2346608 803291874457240079405435 := by
  unfold tailWord_2346608
  simp only [CollatzResearch.WordTrace]
  refine ⟨42793912541323729792340239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57058550055098306389786985 42793912541323729792340239)
  ·
    refine ⟨64190868811985594688510359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42793912541323729792340239 64190868811985594688510359)
    ·
      refine ⟨96286303217978392032765539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64190868811985594688510359 96286303217978392032765539)
      ·
        refine ⟨144429454826967588049148309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96286303217978392032765539 144429454826967588049148309)
        ·
          refine ⟨6770130695014105689803827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144429454826967588049148309 6770130695014105689803827)
          ·
            refine ⟨10155196042521158534705741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6770130695014105689803827 10155196042521158534705741)
            ·
              refine ⟨3808198515945434450514653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10155196042521158534705741 3808198515945434450514653)
              ·
                refine ⟨1428074443479537918942995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3808198515945434450514653 1428074443479537918942995)
                ·
                  refine ⟨2142111665219306878414493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428074443479537918942995 2142111665219306878414493)
                  ·
                    refine ⟨803291874457240079405435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142111665219306878414493 803291874457240079405435)
                    ·
                      rfl

theorem cell22_2346608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 1, 3].length) (baseStart_2346608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346608 prefixEnd_2346608 := by exact prefixLift 2346608
  have htrace : WordTrace (prefixWord ++ tailWord_2346608) baseStart_2346608 baseEnd_2346608 := by
    simpa [prefixWord, tailWord_2346608, baseEnd_2346608] using wordTrace_append hprefix tailTrace_2346608
  have hstable : (prefixWord ++ tailWord_2346608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346608).length < 2 ^ (prefixWord ++ tailWord_2346608).sum := by decide
  have hdescent : baseEnd_2346608 < baseStart_2346608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346625 : List Nat := [1, 2, 4, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2346625 : Nat := 118140960795 + 2346625 * 2 ^ 59
def prefixEnd_2346625 : Nat := 4983230072969 + 3 ^ 40 * 2346625 * 2
def baseEnd_2346625 : Nat := 803297693904657701730383

theorem tailTrace_2346625 : CollatzResearch.WordTrace tailWord_2346625 prefixEnd_2346625 803297693904657701730383 := by
  unfold tailWord_2346625
  simp only [CollatzResearch.WordTrace]
  refine ⟨85588445123585871488049329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57058963415723914325366219 85588445123585871488049329)
  ·
    refine ⟨64191333842689403616036997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85588445123585871488049329 64191333842689403616036997)
    ·
      refine ⟨12035875095504263178006937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64191333842689403616036997 12035875095504263178006937)
      ·
        refine ⟨9026906321628197383505203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12035875095504263178006937 9026906321628197383505203)
        ·
          refine ⟨13540359482442296075257805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9026906321628197383505203 13540359482442296075257805)
          ·
            refine ⟨5077634805915861028221677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13540359482442296075257805 5077634805915861028221677)
            ·
              refine ⟨1904113052218447885583129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5077634805915861028221677 1904113052218447885583129)
              ·
                refine ⟨1428084789163835914187347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1904113052218447885583129 1428084789163835914187347)
                ·
                  refine ⟨2142127183745753871281021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428084789163835914187347 2142127183745753871281021)
                  ·
                    refine ⟨803297693904657701730383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142127183745753871281021 803297693904657701730383)
                    ·
                      rfl

theorem cell22_2346625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2346625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346625 prefixEnd_2346625 := by exact prefixLift 2346625
  have htrace : WordTrace (prefixWord ++ tailWord_2346625) baseStart_2346625 baseEnd_2346625 := by
    simpa [prefixWord, tailWord_2346625, baseEnd_2346625] using wordTrace_append hprefix tailTrace_2346625
  have hstable : (prefixWord ++ tailWord_2346625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346625).length < 2 ^ (prefixWord ++ tailWord_2346625).sum := by decide
  have hdescent : baseEnd_2346625 < baseStart_2346625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346638 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_2346638 : Nat := 118140960795 + 2346638 * 2 ^ 59
def prefixEnd_2346638 : Nat := 4983230072969 + 3 ^ 40 * 2346638 * 2
def baseEnd_2346638 : Nat := 267767381356776667051781

theorem tailTrace_2346638 : CollatzResearch.WordTrace tailWord_2346638 prefixEnd_2346638 267767381356776667051781 := by
  unfold tailWord_2346638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10698614909067346838534071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57059279515025849805515045 10698614909067346838534071)
  ·
    refine ⟨16047922363601020257801107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10698614909067346838534071 16047922363601020257801107)
    ·
      refine ⟨24071883545401530386701661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16047922363601020257801107 24071883545401530386701661)
      ·
        refine ⟨9026956329525573895013123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24071883545401530386701661 9026956329525573895013123)
        ·
          refine ⟨13540434494288360842519685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9026956329525573895013123 13540434494288360842519685)
          ·
            refine ⟨2538831467679067657972441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13540434494288360842519685 2538831467679067657972441)
            ·
              refine ⟨1904123600759300743479331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2538831467679067657972441 1904123600759300743479331)
              ·
                refine ⟨2856185401138951115218997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1904123600759300743479331 2856185401138951115218997)
                ·
                  refine ⟨267767381356776667051781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2856185401138951115218997 267767381356776667051781)
                  ·
                    rfl

theorem cell22_2346638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_2346638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346638 prefixEnd_2346638 := by exact prefixLift 2346638
  have htrace : WordTrace (prefixWord ++ tailWord_2346638) baseStart_2346638 baseEnd_2346638 := by
    simpa [prefixWord, tailWord_2346638, baseEnd_2346638] using wordTrace_append hprefix tailTrace_2346638
  have hstable : (prefixWord ++ tailWord_2346638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346638).length < 2 ^ (prefixWord ++ tailWord_2346638).sum := by decide
  have hdescent : baseEnd_2346638 < baseStart_2346638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346681 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 2, 3]
def baseStart_2346681 : Nat := 118140960795 + 2346681 * 2 ^ 59
def prefixEnd_2346681 : Nat := 4983230072969 + 3 ^ 40 * 2346681 * 2
def baseEnd_2346681 : Nat := 803316863849092222330211

theorem tailTrace_2346681 : CollatzResearch.WordTrace tailWord_2346681 prefixEnd_2346681 803316863849092222330211 := by
  unfold tailWord_2346681
  simp only [CollatzResearch.WordTrace]
  refine ⟨85590487611382993052087897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57060325074255328701391931 85590487611382993052087897)
  ·
    refine ⟨64192865708537244789065923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85590487611382993052087897 64192865708537244789065923)
    ·
      refine ⟨96289298562805867183598885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64192865708537244789065923 96289298562805867183598885)
      ·
        refine ⟨18054243480526100096924791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96289298562805867183598885 18054243480526100096924791)
        ·
          refine ⟨27081365220789150145387187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18054243480526100096924791 27081365220789150145387187)
          ·
            refine ⟨40622047831183725218080781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27081365220789150145387187 40622047831183725218080781)
            ·
              refine ⟨15233267936693896956780293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40622047831183725218080781 15233267936693896956780293)
              ·
                refine ⟨2856237738130105679396305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15233267936693896956780293 2856237738130105679396305)
                ·
                  refine ⟨2142178303597579259547229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2856237738130105679396305 2142178303597579259547229)
                  ·
                    refine ⟨803316863849092222330211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142178303597579259547229 803316863849092222330211)
                    ·
                      rfl

theorem cell22_2346681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_2346681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346681 prefixEnd_2346681 := by exact prefixLift 2346681
  have htrace : WordTrace (prefixWord ++ tailWord_2346681) baseStart_2346681 baseEnd_2346681 := by
    simpa [prefixWord, tailWord_2346681, baseEnd_2346681] using wordTrace_append hprefix tailTrace_2346681
  have hstable : (prefixWord ++ tailWord_2346681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346681).length < 2 ^ (prefixWord ++ tailWord_2346681).sum := by decide
  have hdescent : baseEnd_2346681 < baseStart_2346681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346743 : List Nat := [1, 1, 3, 1, 1, 1, 6, 4, 1, 3]
def baseStart_2346743 : Nat := 118140960795 + 2346743 * 2 ^ 59
def prefixEnd_2346743 : Nat := 4983230072969 + 3 ^ 40 * 2346743 * 2
def baseEnd_2346743 : Nat := 803338087716144727280021

theorem tailTrace_2346743 : CollatzResearch.WordTrace tailWord_2346743 prefixEnd_2346743 803338087716144727280021 := by
  unfold tailWord_2346743
  simp only [CollatzResearch.WordTrace]
  refine ⟨85592748937158377640844883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57061832624772251760563255 85592748937158377640844883)
  ·
    refine ⟨128389123405737566461267325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85592748937158377640844883 128389123405737566461267325)
    ·
      refine ⟨48145921277151587422975247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128389123405737566461267325 48145921277151587422975247)
      ·
        refine ⟨72218881915727381134462871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48145921277151587422975247 72218881915727381134462871)
        ·
          refine ⟨108328322873591071701694307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72218881915727381134462871 108328322873591071701694307)
          ·
            refine ⟨162492484310386607552541461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108328322873591071701694307 162492484310386607552541461)
            ·
              refine ⟨7616835202049372229025381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 162492484310386607552541461 7616835202049372229025381)
              ·
                refine ⟨1428156600384257292942259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7616835202049372229025381 1428156600384257292942259)
                ·
                  refine ⟨2142234900576385939413389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428156600384257292942259 2142234900576385939413389)
                  ·
                    refine ⟨803338087716144727280021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142234900576385939413389 803338087716144727280021)
                    ·
                      rfl

theorem cell22_2346743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_2346743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346743 prefixEnd_2346743 := by exact prefixLift 2346743
  have htrace : WordTrace (prefixWord ++ tailWord_2346743) baseStart_2346743 baseEnd_2346743 := by
    simpa [prefixWord, tailWord_2346743, baseEnd_2346743] using wordTrace_append hprefix tailTrace_2346743
  have hstable : (prefixWord ++ tailWord_2346743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346743).length < 2 ^ (prefixWord ++ tailWord_2346743).sum := by decide
  have hdescent : baseEnd_2346743 < baseStart_2346743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346799 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 3, 5]
def baseStart_2346799 : Nat := 118140960795 + 2346799 * 2 ^ 59
def prefixEnd_2346799 : Nat := 4983230072969 + 3 ^ 40 * 2346799 * 2
def baseEnd_2346799 : Nat := 803357257660579247879849

theorem tailTrace_2346799 : CollatzResearch.WordTrace tailWord_2346799 prefixEnd_2346799 803357257660579247879849 := by
  unfold tailWord_2346799
  simp only [CollatzResearch.WordTrace]
  refine ⟨85594791424955499204883451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57063194283303666136588967 85594791424955499204883451)
  ·
    refine ⟨128392187137433248807325177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85594791424955499204883451 128392187137433248807325177)
    ·
      refine ⟨96294140353074936605493883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128392187137433248807325177 96294140353074936605493883)
      ·
        refine ⟨144441210529612404908240825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96294140353074936605493883 144441210529612404908240825)
        ·
          refine ⟨108330907897209303681180619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144441210529612404908240825 108330907897209303681180619)
          ·
            refine ⟨162496361845813955521770929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108330907897209303681180619 162496361845813955521770929)
            ·
              refine ⟨121872271384360466641328197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162496361845813955521770929 121872271384360466641328197)
              ·
                refine ⟨22851050884567587495249037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121872271384360466641328197 22851050884567587495249037)
                ·
                  refine ⟨8569144081712845310718389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22851050884567587495249037 8569144081712845310718389)
                  ·
                    refine ⟨803357257660579247879849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8569144081712845310718389 803357257660579247879849)
                    ·
                      rfl

theorem cell22_2346799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_2346799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346799 prefixEnd_2346799 := by exact prefixLift 2346799
  have htrace : WordTrace (prefixWord ++ tailWord_2346799) baseStart_2346799 baseEnd_2346799 := by
    simpa [prefixWord, tailWord_2346799, baseEnd_2346799] using wordTrace_append hprefix tailTrace_2346799
  have hstable : (prefixWord ++ tailWord_2346799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346799).length < 2 ^ (prefixWord ++ tailWord_2346799).sum := by decide
  have hdescent : baseEnd_2346799 < baseStart_2346799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346801 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 6]
def baseStart_2346801 : Nat := 118140960795 + 2346801 * 2 ^ 59
def prefixEnd_2346801 : Nat := 4983230072969 + 3 ^ 40 * 2346801 * 2
def baseEnd_2346801 : Nat := 267785980767150636443281

theorem tailTrace_2346801 : CollatzResearch.WordTrace tailWord_2346801 prefixEnd_2346801 267785980767150636443281 := by
  unfold tailWord_2346801
  simp only [CollatzResearch.WordTrace]
  refine ⟨85594864370948253546456257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57063242913965502364304171 85594864370948253546456257)
  ·
    refine ⟨64196148278211190159842193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85594864370948253546456257 64196148278211190159842193)
    ·
      refine ⟨48147111208658392619881645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64196148278211190159842193 48147111208658392619881645)
      ·
        refine ⟨18055166703246897232455617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48147111208658392619881645 18055166703246897232455617)
        ·
          refine ⟨13541375027435172924341713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18055166703246897232455617 13541375027435172924341713)
          ·
            refine ⟨10156031270576379693256285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13541375027435172924341713 10156031270576379693256285)
            ·
              refine ⟨3808511726466142384971107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10156031270576379693256285 3808511726466142384971107)
              ·
                refine ⟨5712767589699213577456661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808511726466142384971107 5712767589699213577456661)
                ·
                  refine ⟨267785980767150636443281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5712767589699213577456661 267785980767150636443281)
                  ·
                    rfl

theorem cell22_2346801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_2346801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346801 prefixEnd_2346801 := by exact prefixLift 2346801
  have htrace : WordTrace (prefixWord ++ tailWord_2346801) baseStart_2346801 baseEnd_2346801 := by
    simpa [prefixWord, tailWord_2346801, baseEnd_2346801] using wordTrace_append hprefix tailTrace_2346801
  have hstable : (prefixWord ++ tailWord_2346801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346801).length < 2 ^ (prefixWord ++ tailWord_2346801).sum := by decide
  have hdescent : baseEnd_2346801 < baseStart_2346801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346846 : List Nat := [4, 4, 14]
def baseStart_2346846 : Nat := 118140960795 + 2346846 * 2 ^ 59
def prefixEnd_2346846 : Nat := 4983230072969 + 3 ^ 40 * 2346846 * 2
def baseEnd_2346846 : Nat := 367340350581201093715

theorem tailTrace_2346846 : CollatzResearch.WordTrace tailWord_2346846 prefixEnd_2346846 367340350581201093715 := by
  unfold tailWord_2346846
  simp only [CollatzResearch.WordTrace]
  refine ⟨10699563206973153278980549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57064337103856817487896261 10699563206973153278980549)
  ·
    refine ⟨2006168101307466239808853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10699563206973153278980549 2006168101307466239808853)
    ·
      refine ⟨367340350581201093715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 2006168101307466239808853 367340350581201093715)
      ·
        rfl

theorem cell22_2346846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 14].length) (baseStart_2346846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346846 prefixEnd_2346846 := by exact prefixLift 2346846
  have htrace : WordTrace (prefixWord ++ tailWord_2346846) baseStart_2346846 baseEnd_2346846 := by
    simpa [prefixWord, tailWord_2346846, baseEnd_2346846] using wordTrace_append hprefix tailTrace_2346846
  have hstable : (prefixWord ++ tailWord_2346846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346846).length < 2 ^ (prefixWord ++ tailWord_2346846).sum := by decide
  have hdescent : baseEnd_2346846 < baseStart_2346846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346850 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2346850 : Nat := 118140960795 + 2346850 * 2 ^ 59
def prefixEnd_2346850 : Nat := 4983230072969 + 3 ^ 40 * 2346850 * 2
def baseEnd_2346850 : Nat := 803374716002832114854693

theorem tailTrace_2346850 : CollatzResearch.WordTrace tailWord_2346850 prefixEnd_2346850 803374716002832114854693 := by
  unfold tailWord_2346850
  simp only [CollatzResearch.WordTrace]
  refine ⟨21399162886942683728747501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57064434365180489943326669 21399162886942683728747501)
  ·
    refine ⟨8024686082603506398280313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21399162886942683728747501 8024686082603506398280313)
    ·
      refine ⟨6018514561952629798710235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8024686082603506398280313 6018514561952629798710235)
      ·
        refine ⟨9027771842928944698065353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6018514561952629798710235 9027771842928944698065353)
        ·
          refine ⟨6770828882196708523549015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9027771842928944698065353 6770828882196708523549015)
          ·
            refine ⟨10156243323295062785323523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6770828882196708523549015 10156243323295062785323523)
            ·
              refine ⟨15234364984942594177985285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10156243323295062785323523 15234364984942594177985285)
              ·
                refine ⟨2856443434676736408372241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15234364984942594177985285 2856443434676736408372241)
                ·
                  refine ⟨2142332576007552306279181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2856443434676736408372241 2142332576007552306279181)
                  ·
                    refine ⟨803374716002832114854693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142332576007552306279181 803374716002832114854693)
                    ·
                      rfl

theorem cell22_2346850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2346850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346850 prefixEnd_2346850 := by exact prefixLift 2346850
  have htrace : WordTrace (prefixWord ++ tailWord_2346850) baseStart_2346850 baseEnd_2346850 := by
    simpa [prefixWord, tailWord_2346850, baseEnd_2346850] using wordTrace_append hprefix tailTrace_2346850
  have hstable : (prefixWord ++ tailWord_2346850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346850).length < 2 ^ (prefixWord ++ tailWord_2346850).sum := by decide
  have hdescent : baseEnd_2346850 < baseStart_2346850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346852 : List Nat := [2, 3, 1, 1, 5, 2, 2, 2, 4]
def baseStart_2346852 : Nat := 118140960795 + 2346852 * 2 ^ 59
def prefixEnd_2346852 : Nat := 4983230072969 + 3 ^ 40 * 2346852 * 2
def baseEnd_2346852 : Nat := 267791800214568258768229

theorem tailTrace_2346852 : CollatzResearch.WordTrace tailWord_2346852 prefixEnd_2346852 267791800214568258768229 := by
  unfold tailWord_2346852
  simp only [CollatzResearch.WordTrace]
  refine ⟨42798362246881744628281405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57064482995842326171041873 42798362246881744628281405)
  ·
    refine ⟨16049385842580654235605527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42798362246881744628281405 16049385842580654235605527)
    ·
      refine ⟨24074078763870981353408291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16049385842580654235605527 24074078763870981353408291)
      ·
        refine ⟨36111118145806472030112437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24074078763870981353408291 36111118145806472030112437)
        ·
          refine ⟨3385417326169356752823041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36111118145806472030112437 3385417326169356752823041)
          ·
            refine ⟨2539062994627017564617281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3385417326169356752823041 2539062994627017564617281)
            ·
              refine ⟨1904297245970263173462961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2539062994627017564617281 1904297245970263173462961)
              ·
                refine ⟨1428222934477697380097221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1904297245970263173462961 1428222934477697380097221)
                ·
                  refine ⟨267791800214568258768229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428222934477697380097221 267791800214568258768229)
                  ·
                    rfl

theorem cell22_2346852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_2346852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346852 prefixEnd_2346852 := by exact prefixLift 2346852
  have htrace : WordTrace (prefixWord ++ tailWord_2346852) baseStart_2346852 baseEnd_2346852 := by
    simpa [prefixWord, tailWord_2346852, baseEnd_2346852] using wordTrace_append hprefix tailTrace_2346852
  have hstable : (prefixWord ++ tailWord_2346852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346852).length < 2 ^ (prefixWord ++ tailWord_2346852).sum := by decide
  have hdescent : baseEnd_2346852 < baseStart_2346852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346908 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 7]
def baseStart_2346908 : Nat := 118140960795 + 2346908 * 2 ^ 59
def prefixEnd_2346908 : Nat := 4983230072969 + 3 ^ 40 * 2346908 * 2
def baseEnd_2346908 : Nat := 267798190196046432301505

theorem tailTrace_2346908 : CollatzResearch.WordTrace tailWord_2346908 prefixEnd_2346908 267798190196046432301505 := by
  unfold tailWord_2346908
  simp only [CollatzResearch.WordTrace]
  refine ⟨42799383490780305410300689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57065844654373740547067585 42799383490780305410300689)
  ·
    refine ⟨32099537618085229057725517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42799383490780305410300689 32099537618085229057725517)
    ·
      refine ⟨12037326606781960896647069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32099537618085229057725517 12037326606781960896647069)
      ·
        refine ⟨4513997477543235336242651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12037326606781960896647069 4513997477543235336242651)
        ·
          refine ⟨6770996216314853004363977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4513997477543235336242651 6770996216314853004363977)
          ·
            refine ⟨5078247162236139753272983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6770996216314853004363977 5078247162236139753272983)
            ·
              refine ⟨7617370743354209629909475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078247162236139753272983 7617370743354209629909475)
              ·
                refine ⟨11426056115031314444864213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7617370743354209629909475 11426056115031314444864213)
                ·
                  refine ⟨267798190196046432301505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11426056115031314444864213 267798190196046432301505)
                  ·
                    rfl

theorem cell22_2346908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_2346908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346908 prefixEnd_2346908 := by exact prefixLift 2346908
  have htrace : WordTrace (prefixWord ++ tailWord_2346908) baseStart_2346908 baseEnd_2346908 := by
    simpa [prefixWord, tailWord_2346908, baseEnd_2346908] using wordTrace_append hprefix tailTrace_2346908
  have hstable : (prefixWord ++ tailWord_2346908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346908).length < 2 ^ (prefixWord ++ tailWord_2346908).sum := by decide
  have hdescent : baseEnd_2346908 < baseStart_2346908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346921 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_2346921 : Nat := 118140960795 + 2346921 * 2 ^ 59
def prefixEnd_2346921 : Nat := 4983230072969 + 3 ^ 40 * 2346921 * 2
def baseEnd_2346921 : Nat := 803399020753811596329475

theorem tailTrace_2346921 : CollatzResearch.WordTrace tailWord_2346921 prefixEnd_2346921 803399020753811596329475 := by
  unfold tailWord_2346921
  simp only [CollatzResearch.WordTrace]
  refine ⟨85599241130513514040824617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57066160753675676027216411 85599241130513514040824617)
  ·
    refine ⟨64199430847885135530618463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85599241130513514040824617 64199430847885135530618463)
    ·
      refine ⟨96299146271827703295927695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64199430847885135530618463 96299146271827703295927695)
      ·
        refine ⟨144448719407741554943891543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96299146271827703295927695 144448719407741554943891543)
        ·
          refine ⟨216673079111612332415837315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144448719407741554943891543 216673079111612332415837315)
          ·
            refine ⟨325009618667418498623755973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216673079111612332415837315 325009618667418498623755973)
            ·
              refine ⟨60939303500140968491954245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 325009618667418498623755973 60939303500140968491954245)
              ·
                refine ⟨11426119406276431592241421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60939303500140968491954245 11426119406276431592241421)
                ·
                  refine ⟨4284794777353661847090533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11426119406276431592241421 4284794777353661847090533)
                  ·
                    refine ⟨803399020753811596329475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4284794777353661847090533 803399020753811596329475)
                    ·
                      rfl

theorem cell22_2346921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_2346921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346921 prefixEnd_2346921 := by exact prefixLift 2346921
  have htrace : WordTrace (prefixWord ++ tailWord_2346921) baseStart_2346921 baseEnd_2346921 := by
    simpa [prefixWord, tailWord_2346921, baseEnd_2346921] using wordTrace_append hprefix tailTrace_2346921
  have hstable : (prefixWord ++ tailWord_2346921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346921).length < 2 ^ (prefixWord ++ tailWord_2346921).sum := by decide
  have hdescent : baseEnd_2346921 < baseStart_2346921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346936 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 6]
def baseStart_2346936 : Nat := 118140960795 + 2346936 * 2 ^ 59
def prefixEnd_2346936 : Nat := 4983230072969 + 3 ^ 40 * 2346936 * 2
def baseEnd_2346936 : Nat := 267801385186785519068143

theorem tailTrace_2346936 : CollatzResearch.WordTrace tailWord_2346936 prefixEnd_2346936 267801385186785519068143 := by
  unfold tailWord_2346936
  simp only [CollatzResearch.WordTrace]
  refine ⟨42799894112729585801310331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57066525483639447735080441 42799894112729585801310331)
  ·
    refine ⟨64199841169094378701965497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42799894112729585801310331 64199841169094378701965497)
    ·
      refine ⟨48149880876820784026474123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64199841169094378701965497 48149880876820784026474123)
      ·
        refine ⟨72224821315231176039711185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48149880876820784026474123 72224821315231176039711185)
        ·
          refine ⟨54168615986423382029783389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72224821315231176039711185 54168615986423382029783389)
          ·
            refine ⟨20313230994908768261168771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54168615986423382029783389 20313230994908768261168771)
            ·
              refine ⟨30469846492363152391753157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20313230994908768261168771 30469846492363152391753157)
              ·
                refine ⟨5713096217318091073453717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30469846492363152391753157 5713096217318091073453717)
                ·
                  refine ⟨267801385186785519068143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5713096217318091073453717 267801385186785519068143)
                  ·
                    rfl

theorem cell22_2346936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_2346936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346936 prefixEnd_2346936 := by exact prefixLift 2346936
  have htrace : WordTrace (prefixWord ++ tailWord_2346936) baseStart_2346936 baseEnd_2346936 := by
    simpa [prefixWord, tailWord_2346936, baseEnd_2346936] using wordTrace_append hprefix tailTrace_2346936
  have hstable : (prefixWord ++ tailWord_2346936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346936).length < 2 ^ (prefixWord ++ tailWord_2346936).sum := by decide
  have hdescent : baseEnd_2346936 < baseStart_2346936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346951 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2346951 : Nat := 118140960795 + 2346951 * 2 ^ 59
def prefixEnd_2346951 : Nat := 4983230072969 + 3 ^ 40 * 2346951 * 2
def baseEnd_2346951 : Nat := 803409290366901518079383

theorem tailTrace_2346951 : CollatzResearch.WordTrace tailWord_2346951 prefixEnd_2346951 803409290366901518079383 := by
  unfold tailWord_2346951
  simp only [CollatzResearch.WordTrace]
  refine ⟨85600335320404829164416707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57066890213603219442944471 85600335320404829164416707)
  ·
    refine ⟨128400502980607243746625061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85600335320404829164416707 128400502980607243746625061)
    ·
      refine ⟨24075094308863858202492199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128400502980607243746625061 24075094308863858202492199)
      ·
        refine ⟨36112641463295787303738299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24075094308863858202492199 36112641463295787303738299)
        ·
          refine ⟨54168962194943680955607449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36112641463295787303738299 54168962194943680955607449)
          ·
            refine ⟨40626721646207760716705587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54168962194943680955607449 40626721646207760716705587)
            ·
              refine ⟨60940082469311641075058381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40626721646207760716705587 60940082469311641075058381)
              ·
                refine ⟨22852530925991865403146893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60940082469311641075058381 22852530925991865403146893)
                ·
                  refine ⟨8569699097246949526180085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22852530925991865403146893 8569699097246949526180085)
                  ·
                    refine ⟨803409290366901518079383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8569699097246949526180085 803409290366901518079383)
                    ·
                      rfl

theorem cell22_2346951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2346951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346951 prefixEnd_2346951 := by exact prefixLift 2346951
  have htrace : WordTrace (prefixWord ++ tailWord_2346951) baseStart_2346951 baseEnd_2346951 := by
    simpa [prefixWord, tailWord_2346951, baseEnd_2346951] using wordTrace_append hprefix tailTrace_2346951
  have hstable : (prefixWord ++ tailWord_2346951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346951).length < 2 ^ (prefixWord ++ tailWord_2346951).sum := by decide
  have hdescent : baseEnd_2346951 < baseStart_2346951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346968 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 4, 3]
def baseStart_2346968 : Nat := 118140960795 + 2346968 * 2 ^ 59
def prefixEnd_2346968 : Nat := 4983230072969 + 3 ^ 40 * 2346968 * 2
def baseEnd_2346968 : Nat := 803415109814319140404331

theorem tailTrace_2346968 : CollatzResearch.WordTrace tailWord_2346968 prefixEnd_2346968 803415109814319140404331 := by
  unfold tailWord_2346968
  simp only [CollatzResearch.WordTrace]
  refine ⟨42800477680671620533892779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57067303574228827378523705 42800477680671620533892779)
  ·
    refine ⟨64200716521007430800839169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42800477680671620533892779 64200716521007430800839169)
    ·
      refine ⟨48150537390755573100629377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64200716521007430800839169 48150537390755573100629377)
      ·
        refine ⟨36112903043066679825472033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48150537390755573100629377 36112903043066679825472033)
        ·
          refine ⟨27084677282300009869104025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36112903043066679825472033 27084677282300009869104025)
          ·
            refine ⟨20313507961725007401828019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27084677282300009869104025 20313507961725007401828019)
            ·
              refine ⟨30470261942587511102742029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20313507961725007401828019 30470261942587511102742029)
              ·
                refine ⟨11426348228470316663528261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30470261942587511102742029 11426348228470316663528261)
                ·
                  refine ⟨2142440292838184374411549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11426348228470316663528261 2142440292838184374411549)
                  ·
                    refine ⟨803415109814319140404331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142440292838184374411549 803415109814319140404331)
                    ·
                      rfl

theorem cell22_2346968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_2346968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346968 prefixEnd_2346968 := by exact prefixLift 2346968
  have htrace : WordTrace (prefixWord ++ tailWord_2346968) baseStart_2346968 baseEnd_2346968 := by
    simpa [prefixWord, tailWord_2346968, baseEnd_2346968] using wordTrace_append hprefix tailTrace_2346968
  have hstable : (prefixWord ++ tailWord_2346968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346968).length < 2 ^ (prefixWord ++ tailWord_2346968).sum := by decide
  have hdescent : baseEnd_2346968 < baseStart_2346968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346970 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_2346970 : Nat := 118140960795 + 2346970 * 2 ^ 59
def prefixEnd_2346970 : Nat := 4983230072969 + 3 ^ 40 * 2346970 * 2
def baseEnd_2346970 : Nat := 267805264818397267284775

theorem tailTrace_2346970 : CollatzResearch.WordTrace tailWord_2346970 prefixEnd_2346970 267805264818397267284775 := by
  unfold tailWord_2346970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21400257076833998852339591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57067352204890663606238909 21400257076833998852339591)
  ·
    refine ⟨32100385615250998278509387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21400257076833998852339591 32100385615250998278509387)
    ·
      refine ⟨48150578422876497417764081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32100385615250998278509387 48150578422876497417764081)
      ·
        refine ⟨36112933817157373063323061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48150578422876497417764081 36112933817157373063323061)
        ·
          refine ⟨3385587545358503724686537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36112933817157373063323061 3385587545358503724686537)
          ·
            refine ⟨2539190659018877793514903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3385587545358503724686537 2539190659018877793514903)
            ·
              refine ⟨3808785988528316690272355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539190659018877793514903 3808785988528316690272355)
              ·
                refine ⟨5713178982792475035408533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3808785988528316690272355 5713178982792475035408533)
                ·
                  refine ⟨267805264818397267284775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5713178982792475035408533 267805264818397267284775)
                  ·
                    rfl

theorem cell22_2346970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_2346970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346970 prefixEnd_2346970 := by exact prefixLift 2346970
  have htrace : WordTrace (prefixWord ++ tailWord_2346970) baseStart_2346970 baseEnd_2346970 := by
    simpa [prefixWord, tailWord_2346970, baseEnd_2346970] using wordTrace_append hprefix tailTrace_2346970
  have hstable : (prefixWord ++ tailWord_2346970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346970).length < 2 ^ (prefixWord ++ tailWord_2346970).sum := by decide
  have hdescent : baseEnd_2346970 < baseStart_2346970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346989 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_2346989 : Nat := 118140960795 + 2346989 * 2 ^ 59
def prefixEnd_2346989 : Nat := 4983230072969 + 3 ^ 40 * 2346989 * 2
def baseEnd_2346989 : Nat := 803422298543482085629267

theorem tailTrace_2346989 : CollatzResearch.WordTrace tailWord_2346989 prefixEnd_2346989 803422298543482085629267 := by
  unfold tailWord_2346989
  simp only [CollatzResearch.WordTrace]
  refine ⟨85601721294267161654300021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57067814196178107769533347 85601721294267161654300021)
  ·
    refine ⟨8025161371337546405090627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85601721294267161654300021 8025161371337546405090627)
    ·
      refine ⟨12037742057006319607635941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8025161371337546405090627 12037742057006319607635941)
      ·
        refine ⟨2257076635688684926431739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12037742057006319607635941 2257076635688684926431739)
        ·
          refine ⟨3385614953533027389647609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257076635688684926431739 3385614953533027389647609)
          ·
            refine ⟨2539211215149770542235707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3385614953533027389647609 2539211215149770542235707)
            ·
              refine ⟨3808816822724655813353561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539211215149770542235707 3808816822724655813353561)
              ·
                refine ⟨2856612617043491860015171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3808816822724655813353561 2856612617043491860015171)
                ·
                  refine ⟨4284918925565237790022757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856612617043491860015171 4284918925565237790022757)
                  ·
                    refine ⟨803422298543482085629267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4284918925565237790022757 803422298543482085629267)
                    ·
                      rfl

theorem cell22_2346989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_2346989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346989 prefixEnd_2346989 := by exact prefixLift 2346989
  have htrace : WordTrace (prefixWord ++ tailWord_2346989) baseStart_2346989 baseEnd_2346989 := by
    simpa [prefixWord, tailWord_2346989, baseEnd_2346989] using wordTrace_append hprefix tailTrace_2346989
  have hstable : (prefixWord ++ tailWord_2346989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346989).length < 2 ^ (prefixWord ++ tailWord_2346989).sum := by decide
  have hdescent : baseEnd_2346989 < baseStart_2346989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347011 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 4, 6]
def baseStart_2347011 : Nat := 118140960795 + 2347011 * 2 ^ 59
def prefixEnd_2347011 : Nat := 4983230072969 + 3 ^ 40 * 2347011 * 2
def baseEnd_2347011 : Nat := 803429829593081361579199

theorem tailTrace_2347011 : CollatzResearch.WordTrace tailWord_2347011 prefixEnd_2347011 803429829593081361579199 := by
  unfold tailWord_2347011
  simp only [CollatzResearch.WordTrace]
  refine ⟨85602523700187459411600887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57068349133458306274400591 85602523700187459411600887)
  ·
    refine ⟨128403785550281189117401331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85602523700187459411600887 128403785550281189117401331)
    ·
      refine ⟨192605678325421783676101997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128403785550281189117401331 192605678325421783676101997)
      ·
        refine ⟨72227129372033168878538249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192605678325421783676101997 72227129372033168878538249)
        ·
          refine ⟨54170347029024876658903687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72227129372033168878538249 54170347029024876658903687)
          ·
            refine ⟨81255520543537314988355531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54170347029024876658903687 81255520543537314988355531)
            ·
              refine ⟨121883280815305972482533297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81255520543537314988355531 121883280815305972482533297)
              ·
                refine ⟨91412460611479479361899973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121883280815305972482533297 91412460611479479361899973)
                ·
                  refine ⟨17139836364652402380356245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91412460611479479361899973 17139836364652402380356245)
                  ·
                    refine ⟨803429829593081361579199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17139836364652402380356245 803429829593081361579199)
                    ·
                      rfl

theorem cell22_2347011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_2347011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347011 prefixEnd_2347011 := by exact prefixLift 2347011
  have htrace : WordTrace (prefixWord ++ tailWord_2347011) baseStart_2347011 baseEnd_2347011 := by
    simpa [prefixWord, tailWord_2347011, baseEnd_2347011] using wordTrace_append hprefix tailTrace_2347011
  have hstable : (prefixWord ++ tailWord_2347011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347011).length < 2 ^ (prefixWord ++ tailWord_2347011).sum := by decide
  have hdescent : baseEnd_2347011 < baseStart_2347011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347021 : List Nat := [1, 7, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2347021 : Nat := 118140960795 + 2347021 * 2 ^ 59
def prefixEnd_2347021 : Nat := 4983230072969 + 3 ^ 40 * 2347021 * 2
def baseEnd_2347021 : Nat := 267811084265814889609723

theorem tailTrace_2347021 : CollatzResearch.WordTrace tailWord_2347021 prefixEnd_2347021 267811084265814889609723 := by
  unfold tailWord_2347021
  simp only [CollatzResearch.WordTrace]
  refine ⟨85602888430151231119464917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57068592286767487412976611 85602888430151231119464917)
  ·
    refine ⟨2006317697581669479362459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 85602888430151231119464917 2006317697581669479362459)
    ·
      refine ⟨3009476546372504219043689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006317697581669479362459 3009476546372504219043689)
      ·
        refine ⟨2257107409779378164282767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3009476546372504219043689 2257107409779378164282767)
        ·
          refine ⟨3385661114669067246424151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257107409779378164282767 3385661114669067246424151)
          ·
            refine ⟨5078491672003600869636227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385661114669067246424151 5078491672003600869636227)
            ·
              refine ⟨7617737508005401304454341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078491672003600869636227 7617737508005401304454341)
              ·
                refine ⟨1428325782751012744585189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7617737508005401304454341 1428325782751012744585189)
                ·
                  refine ⟨267811084265814889609723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428325782751012744585189 267811084265814889609723)
                  ·
                    rfl

theorem cell22_2347021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2347021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347021 prefixEnd_2347021 := by exact prefixLift 2347021
  have htrace : WordTrace (prefixWord ++ tailWord_2347021) baseStart_2347021 baseEnd_2347021 := by
    simpa [prefixWord, tailWord_2347021, baseEnd_2347021] using wordTrace_append hprefix tailTrace_2347021
  have hstable : (prefixWord ++ tailWord_2347021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347021).length < 2 ^ (prefixWord ++ tailWord_2347021).sum := by decide
  have hdescent : baseEnd_2347021 < baseStart_2347021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347043 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 5]
def baseStart_2347043 : Nat := 118140960795 + 2347043 * 2 ^ 59
def prefixEnd_2347043 : Nat := 4983230072969 + 3 ^ 40 * 2347043 * 2
def baseEnd_2347043 : Nat := 267813594615681314926367

theorem tailTrace_2347043 : CollatzResearch.WordTrace tailWord_2347043 prefixEnd_2347043 267813594615681314926367 := by
  unfold tailWord_2347043
  simp only [CollatzResearch.WordTrace]
  refine ⟨85603690836071528876765783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57069127224047685917843855 85603690836071528876765783)
  ·
    refine ⟨128405536254107293315148675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85603690836071528876765783 128405536254107293315148675)
    ·
      refine ⟨192608304381160939972723013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128405536254107293315148675 192608304381160939972723013)
      ·
        refine ⟨36114057071467676244885565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192608304381160939972723013 36114057071467676244885565)
        ·
          refine ⟨13542771401800378591832087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36114057071467676244885565 13542771401800378591832087)
          ·
            refine ⟨20314157102700567887748131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13542771401800378591832087 20314157102700567887748131)
            ·
              refine ⟨30471235654050851831622197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20314157102700567887748131 30471235654050851831622197)
              ·
                refine ⟨2856678342567267359214581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30471235654050851831622197 2856678342567267359214581)
                ·
                  refine ⟨267813594615681314926367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2856678342567267359214581 267813594615681314926367)
                  ·
                    rfl

theorem cell22_2347043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 5].length) (baseStart_2347043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347043 prefixEnd_2347043 := by exact prefixLift 2347043
  have htrace : WordTrace (prefixWord ++ tailWord_2347043) baseStart_2347043 baseEnd_2347043 := by
    simpa [prefixWord, tailWord_2347043, baseEnd_2347043] using wordTrace_append hprefix tailTrace_2347043
  have hstable : (prefixWord ++ tailWord_2347043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347043).length < 2 ^ (prefixWord ++ tailWord_2347043).sum := by decide
  have hdescent : baseEnd_2347043 < baseStart_2347043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347064 : List Nat := [2, 1, 2, 1, 6, 1, 2, 3, 1, 3]
def baseStart_2347064 : Nat := 118140960795 + 2347064 * 2 ^ 59
def prefixEnd_2347064 : Nat := 4983230072969 + 3 ^ 40 * 2347064 * 2
def baseEnd_2347064 : Nat := 803447972576206890004037

theorem tailTrace_2347064 : CollatzResearch.WordTrace tailWord_2347064 prefixEnd_2347064 803447972576206890004037 := by
  unfold tailWord_2347064
  simp only [CollatzResearch.WordTrace]
  refine ⟨42802228384497724731640123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57069637845996966308853497 42802228384497724731640123)
  ·
    refine ⟨64203342576746587097460185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42802228384497724731640123 64203342576746587097460185)
    ·
      refine ⟨48152506932559940323095139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64203342576746587097460185 48152506932559940323095139)
      ·
        refine ⟨72228760398839910484642709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48152506932559940323095139 72228760398839910484642709)
        ·
          refine ⟨3385723143695620803967627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72228760398839910484642709 3385723143695620803967627)
          ·
            refine ⟨5078584715543431205951441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385723143695620803967627 5078584715543431205951441)
            ·
              refine ⟨3808938536657573404463581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5078584715543431205951441 3808938536657573404463581)
              ·
                refine ⟨1428351951246590026673843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3808938536657573404463581 1428351951246590026673843)
                ·
                  refine ⟨2142527926869885040010765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428351951246590026673843 2142527926869885040010765)
                  ·
                    refine ⟨803447972576206890004037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142527926869885040010765 803447972576206890004037)
                    ·
                      rfl

theorem cell22_2347064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_2347064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347064 prefixEnd_2347064 := by exact prefixLift 2347064
  have htrace : WordTrace (prefixWord ++ tailWord_2347064) baseStart_2347064 baseEnd_2347064 := by
    simpa [prefixWord, tailWord_2347064, baseEnd_2347064] using wordTrace_append hprefix tailTrace_2347064
  have hstable : (prefixWord ++ tailWord_2347064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347064).length < 2 ^ (prefixWord ++ tailWord_2347064).sum := by decide
  have hdescent : baseEnd_2347064 < baseStart_2347064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347103 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 1, 5]
def baseStart_2347103 : Nat := 118140960795 + 2347103 * 2 ^ 59
def prefixEnd_2347103 : Nat := 4983230072969 + 3 ^ 40 * 2347103 * 2
def baseEnd_2347103 : Nat := 803461323073223788278917

theorem tailTrace_2347103 : CollatzResearch.WordTrace tailWord_2347103 prefixEnd_2347103 803461323073223788278917 := by
  unfold tailWord_2347103
  simp only [CollatzResearch.WordTrace]
  refine ⟨85605879215854159123949963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57070586143902772749299975 85605879215854159123949963)
  ·
    refine ⟨128408818823781238685924945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85605879215854159123949963 128408818823781238685924945)
    ·
      refine ⟨96306614117835929014443709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128408818823781238685924945 96306614117835929014443709)
      ·
        refine ⟨36114980294188473380416391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96306614117835929014443709 36114980294188473380416391)
        ·
          refine ⟨54172470441282710070624587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36114980294188473380416391 54172470441282710070624587)
          ·
            refine ⟨81258705661924065105936881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54172470441282710070624587 81258705661924065105936881)
            ·
              refine ⟨60944029246443048829452661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81258705661924065105936881 60944029246443048829452661)
              ·
                refine ⟨5713502741854035827761187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60944029246443048829452661 5713502741854035827761187)
                ·
                  refine ⟨8570254112781053741641781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5713502741854035827761187 8570254112781053741641781)
                  ·
                    refine ⟨803461323073223788278917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8570254112781053741641781 803461323073223788278917)
                    ·
                      rfl

theorem cell22_2347103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_2347103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347103 prefixEnd_2347103 := by exact prefixLift 2347103
  have htrace : WordTrace (prefixWord ++ tailWord_2347103) baseStart_2347103 baseEnd_2347103 := by
    simpa [prefixWord, tailWord_2347103, baseEnd_2347103] using wordTrace_append hprefix tailTrace_2347103
  have hstable : (prefixWord ++ tailWord_2347103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347103).length < 2 ^ (prefixWord ++ tailWord_2347103).sum := by decide
  have hdescent : baseEnd_2347103 < baseStart_2347103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347120 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 4, 3]
def baseStart_2347120 : Nat := 118140960795 + 2347120 * 2 ^ 59
def prefixEnd_2347120 : Nat := 4983230072969 + 3 ^ 40 * 2347120 * 2
def baseEnd_2347120 : Nat := 803467142520641410603865

theorem tailTrace_2347120 : CollatzResearch.WordTrace tailWord_2347120 prefixEnd_2347120 803467142520641410603865 := by
  unfold tailWord_2347120
  simp only [CollatzResearch.WordTrace]
  refine ⟨42803249628396285513659407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57070999504528380684879209 42803249628396285513659407)
  ·
    refine ⟨64204874442594428270489111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42803249628396285513659407 64204874442594428270489111)
    ·
      refine ⟨96307311663891642405733667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64204874442594428270489111 96307311663891642405733667)
      ·
        refine ⟨144460967495837463608600501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96307311663891642405733667 144460967495837463608600501)
        ·
          refine ⟨13543215702734762213306297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144460967495837463608600501 13543215702734762213306297)
          ·
            refine ⟨10157411777051071659979723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13543215702734762213306297 10157411777051071659979723)
            ·
              refine ⟨15236117665576607489969585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10157411777051071659979723 15236117665576607489969585)
              ·
                refine ⟨11427088249182455617477189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15236117665576607489969585 11427088249182455617477189)
                ·
                  refine ⟨2142579046721710428276973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11427088249182455617477189 2142579046721710428276973)
                  ·
                    refine ⟨803467142520641410603865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142579046721710428276973 803467142520641410603865)
                    ·
                      rfl

theorem cell22_2347120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_2347120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347120 prefixEnd_2347120 := by exact prefixLift 2347120
  have htrace : WordTrace (prefixWord ++ tailWord_2347120) baseStart_2347120 baseEnd_2347120 := by
    simpa [prefixWord, tailWord_2347120, baseEnd_2347120] using wordTrace_append hprefix tailTrace_2347120
  have hstable : (prefixWord ++ tailWord_2347120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347120).length < 2 ^ (prefixWord ++ tailWord_2347120).sum := by decide
  have hdescent : baseEnd_2347120 < baseStart_2347120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347122 : List Nat := [3, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_2347122 : Nat := 118140960795 + 2347122 * 2 ^ 59
def prefixEnd_2347122 : Nat := 4983230072969 + 3 ^ 40 * 2347122 * 2
def baseEnd_2347122 : Nat := 267822609053838024017953

theorem tailTrace_2347122 : CollatzResearch.WordTrace tailWord_2347122 prefixEnd_2347122 267822609053838024017953 := by
  unfold tailWord_2347122
  simp only [CollatzResearch.WordTrace]
  refine ⟨21401643050696331342222905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57071048135190216912594413 21401643050696331342222905)
  ·
    refine ⟨16051232288022248506667179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21401643050696331342222905 16051232288022248506667179)
    ·
      refine ⟨24076848432033372760000769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16051232288022248506667179 24076848432033372760000769)
      ·
        refine ⟨18057636324025029570000577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24076848432033372760000769 18057636324025029570000577)
        ·
          refine ⟨13543227243018772177500433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18057636324025029570000577 13543227243018772177500433)
          ·
            refine ⟨10157420432264079133125325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13543227243018772177500433 10157420432264079133125325)
            ·
              refine ⟨3809032662099029674921997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10157420432264079133125325 3809032662099029674921997)
              ·
                refine ⟨1428387248287136128095749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3809032662099029674921997 1428387248287136128095749)
                ·
                  refine ⟨267822609053838024017953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428387248287136128095749 267822609053838024017953)
                  ·
                    rfl

theorem cell22_2347122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_2347122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347122 prefixEnd_2347122 := by exact prefixLift 2347122
  have htrace : WordTrace (prefixWord ++ tailWord_2347122) baseStart_2347122 baseEnd_2347122 := by
    simpa [prefixWord, tailWord_2347122, baseEnd_2347122] using wordTrace_append hprefix tailTrace_2347122
  have hstable : (prefixWord ++ tailWord_2347122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347122).length < 2 ^ (prefixWord ++ tailWord_2347122).sum := by decide
  have hdescent : baseEnd_2347122 < baseStart_2347122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347133 : List Nat := [1, 4, 1, 1, 3, 2, 10]
def baseStart_2347133 : Nat := 118140960795 + 2347133 * 2 ^ 59
def prefixEnd_2347133 : Nat := 4983230072969 + 3 ^ 40 * 2347133 * 2
def baseEnd_2347133 : Nat := 29758207136530137408475

theorem tailTrace_2347133 : CollatzResearch.WordTrace tailWord_2347133 prefixEnd_2347133 29758207136530137408475 := by
  unfold tailWord_2347133
  simp only [CollatzResearch.WordTrace]
  refine ⟨85606973405745474247542053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57071315603830316165028035 85606973405745474247542053)
  ·
    refine ⟨16051307513577276421414135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85606973405745474247542053 16051307513577276421414135)
    ·
      refine ⟨24076961270365914632121203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16051307513577276421414135 24076961270365914632121203)
      ·
        refine ⟨36115441905548871948181805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24076961270365914632121203 36115441905548871948181805)
        ·
          refine ⟨13543290714580826980568177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36115441905548871948181805 13543290714580826980568177)
          ·
            refine ⟨10157468035935620235426133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13543290714580826980568177 10157468035935620235426133)
            ·
              refine ⟨29758207136530137408475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10157468035935620235426133 29758207136530137408475)
              ·
                rfl

theorem cell22_2347133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 10].length) (baseStart_2347133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347133 prefixEnd_2347133 := by exact prefixLift 2347133
  have htrace : WordTrace (prefixWord ++ tailWord_2347133) baseStart_2347133 baseEnd_2347133 := by
    simpa [prefixWord, tailWord_2347133, baseEnd_2347133] using wordTrace_append hprefix tailTrace_2347133
  have hstable : (prefixWord ++ tailWord_2347133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347133).length < 2 ^ (prefixWord ++ tailWord_2347133).sum := by decide
  have hdescent : baseEnd_2347133 < baseStart_2347133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347158 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2347158 : Nat := 118140960795 + 2347158 * 2 ^ 59
def prefixEnd_2347158 : Nat := 4983230072969 + 3 ^ 40 * 2347158 * 2
def baseEnd_2347158 : Nat := 803480150697221978153749

theorem tailTrace_2347158 : CollatzResearch.WordTrace tailWord_2347158 prefixEnd_2347158 803480150697221978153749 := by
  unfold tailWord_2347158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350492826915931469825133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57071923487103269011468085 5350492826915931469825133)
  ·
    refine ⟨2006434810093474301184425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5350492826915931469825133 2006434810093474301184425)
    ·
      refine ⟨1504826107570105725888319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2006434810093474301184425 1504826107570105725888319)
      ·
        refine ⟨2257239161355158588832479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504826107570105725888319 2257239161355158588832479)
        ·
          refine ⟨3385858742032737883248719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2257239161355158588832479 3385858742032737883248719)
          ·
            refine ⟨5078788113049106824873079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3385858742032737883248719 5078788113049106824873079)
            ·
              refine ⟨7618182169573660237309619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5078788113049106824873079 7618182169573660237309619)
              ·
                refine ⟨11427273254360490355964429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7618182169573660237309619 11427273254360490355964429)
                ·
                  refine ⟨4285227470385183883486661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11427273254360490355964429 4285227470385183883486661)
                  ·
                    refine ⟨803480150697221978153749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285227470385183883486661 803480150697221978153749)
                    ·
                      rfl

theorem cell22_2347158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2347158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347158 prefixEnd_2347158 := by exact prefixLift 2347158
  have htrace : WordTrace (prefixWord ++ tailWord_2347158) baseStart_2347158 baseEnd_2347158 := by
    simpa [prefixWord, tailWord_2347158, baseEnd_2347158] using wordTrace_append hprefix tailTrace_2347158
  have hstable : (prefixWord ++ tailWord_2347158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347158).length < 2 ^ (prefixWord ++ tailWord_2347158).sum := by decide
  have hdescent : baseEnd_2347158 < baseStart_2347158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347195 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 5]
def baseStart_2347195 : Nat := 118140960795 + 2347195 * 2 ^ 59
def prefixEnd_2347195 : Nat := 4983230072969 + 3 ^ 40 * 2347195 * 2
def baseEnd_2347195 : Nat := 267830938851122071659545

theorem tailTrace_2347195 : CollatzResearch.WordTrace tailWord_2347195 prefixEnd_2347195 267830938851122071659545 := by
  unfold tailWord_2347195
  simp only [CollatzResearch.WordTrace]
  refine ⟨85609234731520858836299039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57072823154347239224199359 85609234731520858836299039)
  ·
    refine ⟨128413852097281288254448559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85609234731520858836299039 128413852097281288254448559)
    ·
      refine ⟨192620778145921932381672839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128413852097281288254448559 192620778145921932381672839)
      ·
        refine ⟨288931167218882898572509259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192620778145921932381672839 288931167218882898572509259)
        ·
          refine ⟨433396750828324347858763889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288931167218882898572509259 433396750828324347858763889)
          ·
            refine ⟨325047563121243260894072917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433396750828324347858763889 325047563121243260894072917)
            ·
              refine ⟨3809151130327069463602417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 325047563121243260894072917 3809151130327069463602417)
              ·
                refine ⟨2856863347745302097701813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3809151130327069463602417 2856863347745302097701813)
                ·
                  refine ⟨267830938851122071659545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2856863347745302097701813 267830938851122071659545)
                  ·
                    rfl

theorem cell22_2347195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 5].length) (baseStart_2347195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347195 prefixEnd_2347195 := by exact prefixLift 2347195
  have htrace : WordTrace (prefixWord ++ tailWord_2347195) baseStart_2347195 baseEnd_2347195 := by
    simpa [prefixWord, tailWord_2347195, baseEnd_2347195] using wordTrace_append hprefix tailTrace_2347195
  have hstable : (prefixWord ++ tailWord_2347195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347195).length < 2 ^ (prefixWord ++ tailWord_2347195).sum := by decide
  have hdescent : baseEnd_2347195 < baseStart_2347195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347210 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_2347210 : Nat := 118140960795 + 2347210 * 2 ^ 59
def prefixEnd_2347210 : Nat := 4983230072969 + 3 ^ 40 * 2347210 * 2
def baseEnd_2347210 : Nat := 803497951359911175853589

theorem tailTrace_2347210 : CollatzResearch.WordTrace tailWord_2347210 prefixEnd_2347210 803497951359911175853589 := by
  unfold tailWord_2347210
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402445456616629099523771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57073187884311010932063389 21402445456616629099523771)
  ·
    refine ⟨32103668184924943649285657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21402445456616629099523771 32103668184924943649285657)
    ·
      refine ⟨24077751138693707736964243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32103668184924943649285657 24077751138693707736964243)
      ·
        refine ⟨36116626708040561605446365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24077751138693707736964243 36116626708040561605446365)
        ·
          refine ⟨13543735015515210602042387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36116626708040561605446365 13543735015515210602042387)
          ·
            refine ⟨20315602523272815903063581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13543735015515210602042387 20315602523272815903063581)
            ·
              refine ⟨7618350946227305963648843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20315602523272815903063581 7618350946227305963648843)
              ·
                refine ⟨11427526419340958945473265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7618350946227305963648843 11427526419340958945473265)
                ·
                  refine ⟨8570644814505719209104949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11427526419340958945473265 8570644814505719209104949)
                  ·
                    refine ⟨803497951359911175853589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8570644814505719209104949 803497951359911175853589)
                    ·
                      rfl

theorem cell22_2347210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_2347210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347210 prefixEnd_2347210 := by exact prefixLift 2347210
  have htrace : WordTrace (prefixWord ++ tailWord_2347210) baseStart_2347210 baseEnd_2347210 := by
    simpa [prefixWord, tailWord_2347210, baseEnd_2347210] using wordTrace_append hprefix tailTrace_2347210
  have hstable : (prefixWord ++ tailWord_2347210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347210).length < 2 ^ (prefixWord ++ tailWord_2347210).sum := by decide
  have hdescent : baseEnd_2347210 < baseStart_2347210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347225 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_2347225 : Nat := 118140960795 + 2347225 * 2 ^ 59
def prefixEnd_2347225 : Nat := 4983230072969 + 3 ^ 40 * 2347225 * 2
def baseEnd_2347225 : Nat := 803503086166456136728543

theorem tailTrace_2347225 : CollatzResearch.WordTrace tailWord_2347225 prefixEnd_2347225 803503086166456136728543 := by
  unfold tailWord_2347225
  simp only [CollatzResearch.WordTrace]
  refine ⟨85610328921412173959891129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57073552614274782639927419 85610328921412173959891129)
  ·
    refine ⟨64207746691059130469918347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85610328921412173959891129 64207746691059130469918347)
    ·
      refine ⟨96311620036588695704877521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64207746691059130469918347 96311620036588695704877521)
      ·
        refine ⟨72233715027441521778658141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96311620036588695704877521 72233715027441521778658141)
        ·
          refine ⟨27087643135290570666996803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72233715027441521778658141 27087643135290570666996803)
          ·
            refine ⟨40631464702935856000495205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27087643135290570666996803 40631464702935856000495205)
            ·
              refine ⟨7618399631800473000092851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40631464702935856000495205 7618399631800473000092851)
              ·
                refine ⟨11427599447700709500139277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7618399631800473000092851 11427599447700709500139277)
                ·
                  refine ⟨4285349792887766062552229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11427599447700709500139277 4285349792887766062552229)
                  ·
                    refine ⟨803503086166456136728543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285349792887766062552229 803503086166456136728543)
                    ·
                      rfl

theorem cell22_2347225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_2347225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347225 prefixEnd_2347225 := by exact prefixLift 2347225
  have htrace : WordTrace (prefixWord ++ tailWord_2347225) baseStart_2347225 baseEnd_2347225 := by
    simpa [prefixWord, tailWord_2347225, baseEnd_2347225] using wordTrace_append hprefix tailTrace_2347225
  have hstable : (prefixWord ++ tailWord_2347225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347225).length < 2 ^ (prefixWord ++ tailWord_2347225).sum := by decide
  have hdescent : baseEnd_2347225 < baseStart_2347225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347242 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_2347242 : Nat := 118140960795 + 2347242 * 2 ^ 59
def prefixEnd_2347242 : Nat := 4983230072969 + 3 ^ 40 * 2347242 * 2
def baseEnd_2347242 : Nat := 803508905613873759053491

theorem tailTrace_2347242 : CollatzResearch.WordTrace tailWord_2347242 prefixEnd_2347242 803508905613873759053491 := by
  unfold tailWord_2347242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21402737240587646465814995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57073965974900390575506653 21402737240587646465814995)
  ·
    refine ⟨32104105860881469698722493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21402737240587646465814995 32104105860881469698722493)
    ·
      refine ⟨12039039697830551137020935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32104105860881469698722493 12039039697830551137020935)
      ·
        refine ⟨18058559546745826705531403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12039039697830551137020935 18058559546745826705531403)
        ·
          refine ⟨27087839320118740058297105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18058559546745826705531403 27087839320118740058297105)
          ·
            refine ⟨20315879490089055043722829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27087839320118740058297105 20315879490089055043722829)
            ·
              refine ⟨7618454808783395641396061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20315879490089055043722829 7618454808783395641396061)
              ·
                refine ⟨2856920553293773365523523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7618454808783395641396061 2856920553293773365523523)
                ·
                  refine ⟨4285380829940660048285285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2856920553293773365523523 4285380829940660048285285)
                  ·
                    refine ⟨803508905613873759053491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285380829940660048285285 803508905613873759053491)
                    ·
                      rfl

theorem cell22_2347242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_2347242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347242 prefixEnd_2347242 := by exact prefixLift 2347242
  have htrace : WordTrace (prefixWord ++ tailWord_2347242) baseStart_2347242 baseEnd_2347242 := by
    simpa [prefixWord, tailWord_2347242, baseEnd_2347242] using wordTrace_append hprefix tailTrace_2347242
  have hstable : (prefixWord ++ tailWord_2347242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347242).length < 2 ^ (prefixWord ++ tailWord_2347242).sum := by decide
  have hdescent : baseEnd_2347242 < baseStart_2347242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347272 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_2347272 : Nat := 118140960795 + 2347272 * 2 ^ 59
def prefixEnd_2347272 : Nat := 4983230072969 + 3 ^ 40 * 2347272 * 2
def baseEnd_2347272 : Nat := 803519175226963680803399

theorem tailTrace_2347272 : CollatzResearch.WordTrace tailWord_2347272 prefixEnd_2347272 803519175226963680803399 := by
  unfold tailWord_2347272
  simp only [CollatzResearch.WordTrace]
  refine ⟨42806021576120950493426035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57074695434827933991234713 42806021576120950493426035)
  ·
    refine ⟨64209032364181425740139053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42806021576120950493426035 64209032364181425740139053)
    ·
      refine ⟨24078387136568034652552145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64209032364181425740139053 24078387136568034652552145)
      ·
        refine ⟨18058790352426025989414109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24078387136568034652552145 18058790352426025989414109)
        ·
          refine ⟨6772046382159759746030291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18058790352426025989414109 6772046382159759746030291)
          ·
            refine ⟨10158069573239639619045437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6772046382159759746030291 10158069573239639619045437)
            ·
              refine ⟨3809276089964864857142039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10158069573239639619045437 3809276089964864857142039)
              ·
                refine ⟨5713914134947297285713059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3809276089964864857142039 5713914134947297285713059)
                ·
                  refine ⟨8570871202420945928569589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5713914134947297285713059 8570871202420945928569589)
                  ·
                    refine ⟨803519175226963680803399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8570871202420945928569589 803519175226963680803399)
                    ·
                      rfl

theorem cell22_2347272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_2347272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347272 prefixEnd_2347272 := by exact prefixLift 2347272
  have htrace : WordTrace (prefixWord ++ tailWord_2347272) baseStart_2347272 baseEnd_2347272 := by
    simpa [prefixWord, tailWord_2347272, baseEnd_2347272] using wordTrace_append hprefix tailTrace_2347272
  have hstable : (prefixWord ++ tailWord_2347272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347272).length < 2 ^ (prefixWord ++ tailWord_2347272).sum := by decide
  have hdescent : baseEnd_2347272 < baseStart_2347272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347304 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2347304 : Nat := 118140960795 + 2347304 * 2 ^ 59
def prefixEnd_2347304 : Nat := 4983230072969 + 3 ^ 40 * 2347304 * 2
def baseEnd_2347304 : Nat := 803530129480926264003301

theorem tailTrace_2347304 : CollatzResearch.WordTrace tailWord_2347304 prefixEnd_2347304 803530129480926264003301 := by
  unfold tailWord_2347304
  simp only [CollatzResearch.WordTrace]
  refine ⟨42806605144062985226008483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57075473525417313634677977 42806605144062985226008483)
  ·
    refine ⟨64209907716094477839012725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42806605144062985226008483 64209907716094477839012725)
    ·
      refine ⟨6019678848383857297407443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64209907716094477839012725 6019678848383857297407443)
      ·
        refine ⟨9029518272575785946111165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6019678848383857297407443 9029518272575785946111165)
        ·
          refine ⟨3386069352215919729791687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9029518272575785946111165 3386069352215919729791687)
          ·
            refine ⟨5079104028323879594687531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3386069352215919729791687 5079104028323879594687531)
            ·
              refine ⟨7618656042485819392031297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079104028323879594687531 7618656042485819392031297)
              ·
                refine ⟨5713992031864364544023473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7618656042485819392031297 5713992031864364544023473)
                ·
                  refine ⟨4285494023898273408017605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5713992031864364544023473 4285494023898273408017605)
                  ·
                    refine ⟨803530129480926264003301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4285494023898273408017605 803530129480926264003301)
                    ·
                      rfl

theorem cell22_2347304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2347304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347304 prefixEnd_2347304 := by exact prefixLift 2347304
  have htrace : WordTrace (prefixWord ++ tailWord_2347304) baseStart_2347304 baseEnd_2347304 := by
    simpa [prefixWord, tailWord_2347304, baseEnd_2347304] using wordTrace_append hprefix tailTrace_2347304
  have hstable : (prefixWord ++ tailWord_2347304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347304).length < 2 ^ (prefixWord ++ tailWord_2347304).sum := by decide
  have hdescent : baseEnd_2347304 < baseStart_2347304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347315 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 2, 6]
def baseStart_2347315 : Nat := 118140960795 + 2347315 * 2 ^ 59
def prefixEnd_2347315 : Nat := 4983230072969 + 3 ^ 40 * 2347315 * 2
def baseEnd_2347315 : Nat := 803533895005725901978267

theorem tailTrace_2347315 : CollatzResearch.WordTrace tailWord_2347315 prefixEnd_2347315 803533895005725901978267 := by
  unfold tailWord_2347315
  simp only [CollatzResearch.WordTrace]
  refine ⟨85613611491086119330667399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57075740994057412887111599 85613611491086119330667399)
  ·
    refine ⟨128420417236629178996001099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85613611491086119330667399 128420417236629178996001099)
    ·
      refine ⟨192630625854943768494001649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128420417236629178996001099 192630625854943768494001649)
      ·
        refine ⟨144472969391207826370501237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192630625854943768494001649 144472969391207826370501237)
        ·
          refine ⟨13544340880425733722234491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144472969391207826370501237 13544340880425733722234491)
          ·
            refine ⟨20316511320638600583351737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13544340880425733722234491 20316511320638600583351737)
            ·
              refine ⟨15237383490478950437513803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20316511320638600583351737 15237383490478950437513803)
              ·
                refine ⟨22856075235718425656270705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15237383490478950437513803 22856075235718425656270705)
                ·
                  refine ⟨17142056426788819242203029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22856075235718425656270705 17142056426788819242203029)
                  ·
                    refine ⟨803533895005725901978267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17142056426788819242203029 803533895005725901978267)
                    ·
                      rfl

theorem cell22_2347315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_2347315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347315 prefixEnd_2347315 := by exact prefixLift 2347315
  have htrace : WordTrace (prefixWord ++ tailWord_2347315) baseStart_2347315 baseEnd_2347315 := by
    simpa [prefixWord, tailWord_2347315, baseEnd_2347315] using wordTrace_append hprefix tailTrace_2347315
  have hstable : (prefixWord ++ tailWord_2347315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347315).length < 2 ^ (prefixWord ++ tailWord_2347315).sum := by decide
  have hdescent : baseEnd_2347315 < baseStart_2347315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347368 : List Nat := [2, 1, 4, 2, 2, 1, 4, 2, 1, 3]
def baseStart_2347368 : Nat := 118140960795 + 2347368 * 2 ^ 59
def prefixEnd_2347368 : Nat := 4983230072969 + 3 ^ 40 * 2347368 * 2
def baseEnd_2347368 : Nat := 803552037988851430403105

theorem tailTrace_2347368 : CollatzResearch.WordTrace tailWord_2347368 prefixEnd_2347368 803552037988851430403105 := by
  unfold tailWord_2347368
  simp only [CollatzResearch.WordTrace]
  refine ⟨42807772279947054691173379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57077029706596072921564505 42807772279947054691173379)
  ·
    refine ⟨64211658419920582036760069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42807772279947054691173379 64211658419920582036760069)
    ·
      refine ⟨12039685953735109131892513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64211658419920582036760069 12039685953735109131892513)
      ·
        refine ⟨9029764465301331848919385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12039685953735109131892513 9029764465301331848919385)
        ·
          refine ⟨6772323348975998886689539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9029764465301331848919385 6772323348975998886689539)
          ·
            refine ⟨10158485023463998330034309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6772323348975998886689539 10158485023463998330034309)
            ·
              refine ⟨1904715941899499686881433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10158485023463998330034309 1904715941899499686881433)
              ·
                refine ⟨1428536956424624765161075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1904715941899499686881433 1428536956424624765161075)
                ·
                  refine ⟨2142805434636937147741613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428536956424624765161075 2142805434636937147741613)
                  ·
                    refine ⟨803552037988851430403105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142805434636937147741613 803552037988851430403105)
                    ·
                      rfl

theorem cell22_2347368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_2347368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347368 prefixEnd_2347368 := by exact prefixLift 2347368
  have htrace : WordTrace (prefixWord ++ tailWord_2347368) baseStart_2347368 baseEnd_2347368 := by
    simpa [prefixWord, tailWord_2347368, baseEnd_2347368] using wordTrace_append hprefix tailTrace_2347368
  have hstable : (prefixWord ++ tailWord_2347368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347368).length < 2 ^ (prefixWord ++ tailWord_2347368).sum := by decide
  have hdescent : baseEnd_2347368 < baseStart_2347368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347424 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 4, 3]
def baseStart_2347424 : Nat := 118140960795 + 2347424 * 2 ^ 59
def prefixEnd_2347424 : Nat := 4983230072969 + 3 ^ 40 * 2347424 * 2
def baseEnd_2347424 : Nat := 803571207933285951002933

theorem tailTrace_2347424 : CollatzResearch.WordTrace tailWord_2347424 prefixEnd_2347424 803571207933285951002933 := by
  unfold tailWord_2347424
  simp only [CollatzResearch.WordTrace]
  refine ⟨42808793523845615473192663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57078391365127487297590217 42808793523845615473192663)
  ·
    refine ⟨64213190285768423209788995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42808793523845615473192663 64213190285768423209788995)
    ·
      refine ⟨96319785428652634814683493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64213190285768423209788995 96319785428652634814683493)
      ·
        refine ⟨18059959767872369027753155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96319785428652634814683493 18059959767872369027753155)
        ·
          refine ⟨27089939651808553541629733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18059959767872369027753155 27089939651808553541629733)
          ·
            refine ⟨5079363684714103789055575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27089939651808553541629733 5079363684714103789055575)
            ·
              refine ⟨7619045527071155683583363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079363684714103789055575 7619045527071155683583363)
              ·
                refine ⟨11428568290606733525375045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7619045527071155683583363 11428568290606733525375045)
                ·
                  refine ⟨2142856554488762536007821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11428568290606733525375045 2142856554488762536007821)
                  ·
                    refine ⟨803571207933285951002933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2142856554488762536007821 803571207933285951002933)
                    ·
                      rfl

theorem cell22_2347424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_2347424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347424 prefixEnd_2347424 := by exact prefixLift 2347424
  have htrace : WordTrace (prefixWord ++ tailWord_2347424) baseStart_2347424 baseEnd_2347424 := by
    simpa [prefixWord, tailWord_2347424, baseEnd_2347424] using wordTrace_append hprefix tailTrace_2347424
  have hstable : (prefixWord ++ tailWord_2347424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347424).length < 2 ^ (prefixWord ++ tailWord_2347424).sum := by decide
  have hdescent : baseEnd_2347424 < baseStart_2347424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347454 : List Nat := [4, 2, 1, 1, 1, 1, 6, 6]
def baseStart_2347454 : Nat := 118140960795 + 2347454 * 2 ^ 59
def prefixEnd_2347454 : Nat := 4983230072969 + 3 ^ 40 * 2347454 * 2
def baseEnd_2347454 : Nat := 89286830838486208083649

theorem tailTrace_2347454 : CollatzResearch.WordTrace tailWord_2347454 prefixEnd_2347454 89286830838486208083649 := by
  unfold tailWord_2347454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10702335154697818258747177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57079120825055030713318277 10702335154697818258747177)
  ·
    refine ⟨8026751366023363694060383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10702335154697818258747177 8026751366023363694060383)
    ·
      refine ⟨12040127049035045541090575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8026751366023363694060383 12040127049035045541090575)
      ·
        refine ⟨18060190573552568311635863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12040127049035045541090575 18060190573552568311635863)
        ·
          refine ⟨27090285860328852467453795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18060190573552568311635863 27090285860328852467453795)
          ·
            refine ⟨40635428790493278701180693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27090285860328852467453795 40635428790493278701180693)
            ·
              refine ⟨1904785724554372439117845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40635428790493278701180693 1904785724554372439117845)
              ·
                refine ⟨89286830838486208083649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1904785724554372439117845 89286830838486208083649)
                ·
                  rfl

theorem cell22_2347454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_2347454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347454 prefixEnd_2347454 := by exact prefixLift 2347454
  have htrace : WordTrace (prefixWord ++ tailWord_2347454) baseStart_2347454 baseEnd_2347454 := by
    simpa [prefixWord, tailWord_2347454, baseEnd_2347454] using wordTrace_append hprefix tailTrace_2347454
  have hstable : (prefixWord ++ tailWord_2347454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347454).length < 2 ^ (prefixWord ++ tailWord_2347454).sum := by decide
  have hdescent : baseEnd_2347454 < baseStart_2347454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347460 : List Nat := [2, 3, 3, 2, 3, 1, 1, 3, 4]
def baseStart_2347460 : Nat := 118140960795 + 2347460 * 2 ^ 59
def prefixEnd_2347460 : Nat := 4983230072969 + 3 ^ 40 * 2347460 * 2
def baseEnd_2347460 : Nat := 267861177156331285700941

theorem tailTrace_2347460 : CollatzResearch.WordTrace tailWord_2347460 prefixEnd_2347460 267861177156331285700941 := by
  unfold tailWord_2347460
  simp only [CollatzResearch.WordTrace]
  refine ⟨42809450037780404547347917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57079266717040539396463889 42809450037780404547347917)
  ·
    refine ⟨16053543764167651705255469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42809450037780404547347917 16053543764167651705255469)
    ·
      refine ⟨6020078911562869389470801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16053543764167651705255469 6020078911562869389470801)
      ·
        refine ⟨4515059183672152042103101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6020078911562869389470801 4515059183672152042103101)
        ·
          refine ⟨1693147193877057015788663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4515059183672152042103101 1693147193877057015788663)
          ·
            refine ⟨2539720790815585523682995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693147193877057015788663 2539720790815585523682995)
            ·
              refine ⟨3809581186223378285524493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539720790815585523682995 3809581186223378285524493)
              ·
                refine ⟨1428592944833766857071685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3809581186223378285524493 1428592944833766857071685)
                ·
                  refine ⟨267861177156331285700941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428592944833766857071685 267861177156331285700941)
                  ·
                    rfl

theorem cell22_2347460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_2347460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347460 prefixEnd_2347460 := by exact prefixLift 2347460
  have htrace : WordTrace (prefixWord ++ tailWord_2347460) baseStart_2347460 baseEnd_2347460 := by
    simpa [prefixWord, tailWord_2347460, baseEnd_2347460] using wordTrace_append hprefix tailTrace_2347460
  have hstable : (prefixWord ++ tailWord_2347460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347460).length < 2 ^ (prefixWord ++ tailWord_2347460).sum := by decide
  have hdescent : baseEnd_2347460 < baseStart_2347460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347482 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_2347482 : Nat := 118140960795 + 2347482 * 2 ^ 59
def prefixEnd_2347482 : Nat := 4983230072969 + 3 ^ 40 * 2347482 * 2
def baseEnd_2347482 : Nat := 267863687506197711017585

theorem tailTrace_2347482 : CollatzResearch.WordTrace tailWord_2347482 prefixEnd_2347482 267863687506197711017585 := by
  unfold tailWord_2347482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21404925620370276712999175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57079801654320737901331133 21404925620370276712999175)
  ·
    refine ⟨32107388430555415069498763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21404925620370276712999175 32107388430555415069498763)
    ·
      refine ⟨48161082645833122604248145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32107388430555415069498763 48161082645833122604248145)
      ·
        refine ⟨36120811984374841953186109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48161082645833122604248145 36120811984374841953186109)
        ·
          refine ⟨13545304494140565732444791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36120811984374841953186109 13545304494140565732444791)
          ·
            refine ⟨20317956741210848598667187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13545304494140565732444791 20317956741210848598667187)
            ·
              refine ⟨30476935111816272898000781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20317956741210848598667187 30476935111816272898000781)
              ·
                refine ⟨11428850666931102336750293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30476935111816272898000781 11428850666931102336750293)
                ·
                  refine ⟨267863687506197711017585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11428850666931102336750293 267863687506197711017585)
                  ·
                    rfl

theorem cell22_2347482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_2347482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347482 prefixEnd_2347482 := by exact prefixLift 2347482
  have htrace : WordTrace (prefixWord ++ tailWord_2347482) baseStart_2347482 baseEnd_2347482 := by
    simpa [prefixWord, tailWord_2347482, baseEnd_2347482] using wordTrace_append hprefix tailTrace_2347482
  have hstable : (prefixWord ++ tailWord_2347482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347482).length < 2 ^ (prefixWord ++ tailWord_2347482).sum := by decide
  have hdescent : baseEnd_2347482 < baseStart_2347482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347533 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2347533 : Nat := 118140960795 + 2347533 * 2 ^ 59
def prefixEnd_2347533 : Nat := 4983230072969 + 3 ^ 40 * 2347533 * 2
def baseEnd_2347533 : Nat := 267869506953615333342533

theorem tailTrace_2347533 : CollatzResearch.WordTrace tailWord_2347533 prefixEnd_2347533 267869506953615333342533 := by
  unfold tailWord_2347533
  simp only [CollatzResearch.WordTrace]
  refine ⟨85621562604296342562103253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57081041736197561708068835 85621562604296342562103253)
  ·
    refine ⟨2006755373538195528799295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 85621562604296342562103253 2006755373538195528799295)
    ·
      refine ⟨3010133060307293293198943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006755373538195528799295 3010133060307293293198943)
      ·
        refine ⟨4515199590460939939798415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3010133060307293293198943 4515199590460939939798415)
        ·
          refine ⟨6772799385691409909697623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4515199590460939939798415 6772799385691409909697623)
          ·
            refine ⟨10159199078537114864546435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6772799385691409909697623 10159199078537114864546435)
            ·
              refine ⟨15238798617805672296819653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10159199078537114864546435 15238798617805672296819653)
              ·
                refine ⟨2857274740838563555653685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15238798617805672296819653 2857274740838563555653685)
                ·
                  refine ⟨267869506953615333342533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2857274740838563555653685 267869506953615333342533)
                  ·
                    rfl

theorem cell22_2347533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2347533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347533 prefixEnd_2347533 := by exact prefixLift 2347533
  have htrace : WordTrace (prefixWord ++ tailWord_2347533) baseStart_2347533 baseEnd_2347533 := by
    simpa [prefixWord, tailWord_2347533, baseEnd_2347533] using wordTrace_append hprefix tailTrace_2347533
  have hstable : (prefixWord ++ tailWord_2347533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347533).length < 2 ^ (prefixWord ++ tailWord_2347533).sum := by decide
  have hdescent : baseEnd_2347533 < baseStart_2347533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347587 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 1, 9]
def baseStart_2347587 : Nat := 118140960795 + 2347587 * 2 ^ 59
def prefixEnd_2347587 : Nat := 4983230072969 + 3 ^ 40 * 2347587 * 2
def baseEnd_2347587 : Nat := 803627006164407859177433

theorem tailTrace_2347587 : CollatzResearch.WordTrace tailWord_2347587 prefixEnd_2347587 803627006164407859177433 := by
  unfold tailWord_2347587
  simp only [CollatzResearch.WordTrace]
  refine ⟨85623532146100709784569015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57082354764067139856379343 85623532146100709784569015)
  ·
    refine ⟨128435298219151064676853523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85623532146100709784569015 128435298219151064676853523)
    ·
      refine ⟨192652947328726597015280285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128435298219151064676853523 192652947328726597015280285)
      ·
        refine ⟨72244855248272473880730107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192652947328726597015280285 72244855248272473880730107)
        ·
          refine ⟨108367282872408710821095161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72244855248272473880730107 108367282872408710821095161)
          ·
            refine ⟨81275462154306533115821371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108367282872408710821095161 81275462154306533115821371)
            ·
              refine ⟨121913193231459799673732057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81275462154306533115821371 121913193231459799673732057)
              ·
                refine ⟨91434894923594849755299043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121913193231459799673732057 91434894923594849755299043)
                ·
                  refine ⟨137152342385392274632948565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91434894923594849755299043 137152342385392274632948565)
                  ·
                    refine ⟨803627006164407859177433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 137152342385392274632948565 803627006164407859177433)
                    ·
                      rfl

theorem cell22_2347587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_2347587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347587 prefixEnd_2347587 := by exact prefixLift 2347587
  have htrace : WordTrace (prefixWord ++ tailWord_2347587) baseStart_2347587 baseEnd_2347587 := by
    simpa [prefixWord, tailWord_2347587, baseEnd_2347587] using wordTrace_append hprefix tailTrace_2347587
  have hstable : (prefixWord ++ tailWord_2347587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347587).length < 2 ^ (prefixWord ++ tailWord_2347587).sum := by decide
  have hdescent : baseEnd_2347587 < baseStart_2347587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347655 : List Nat := [1, 1, 4, 2, 1, 2, 5, 2, 1, 3]
def baseStart_2347655 : Nat := 118140960795 + 2347655 * 2 ^ 59
def prefixEnd_2347655 : Nat := 4983230072969 + 3 ^ 40 * 2347655 * 2
def baseEnd_2347655 : Nat := 803650283954078348477225

theorem tailTrace_2347655 : CollatzResearch.WordTrace tailWord_2347655 prefixEnd_2347655 803650283954078348477225 := by
  unfold tailWord_2347655
  simp only [CollatzResearch.WordTrace]
  refine ⟨85626012309854357398044419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57084008206569571598696279 85626012309854357398044419)
  ·
    refine ⟨128439018464781536097066629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85626012309854357398044419 128439018464781536097066629)
    ·
      refine ⟨24082315962146538018199993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128439018464781536097066629 24082315962146538018199993)
      ·
        refine ⟨18061736971609903513649995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24082315962146538018199993 18061736971609903513649995)
        ·
          refine ⟨27092605457414855270474993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18061736971609903513649995 27092605457414855270474993)
          ·
            refine ⟨20319454093061141452856245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27092605457414855270474993 20319454093061141452856245)
            ·
              refine ⟨1904948821224482011205273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20319454093061141452856245 1904948821224482011205273)
              ·
                refine ⟨1428711615918361508403955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1904948821224482011205273 1428711615918361508403955)
                ·
                  refine ⟨2143067423877542262605933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428711615918361508403955 2143067423877542262605933)
                  ·
                    refine ⟨803650283954078348477225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143067423877542262605933 803650283954078348477225)
                    ·
                      rfl

theorem cell22_2347655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_2347655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347655 prefixEnd_2347655 := by exact prefixLift 2347655
  have htrace : WordTrace (prefixWord ++ tailWord_2347655) baseStart_2347655 baseEnd_2347655 := by
    simpa [prefixWord, tailWord_2347655, baseEnd_2347655] using wordTrace_append hprefix tailTrace_2347655
  have hstable : (prefixWord ++ tailWord_2347655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347655).length < 2 ^ (prefixWord ++ tailWord_2347655).sum := by decide
  have hdescent : baseEnd_2347655 < baseStart_2347655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347668 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 5]
def baseStart_2347668 : Nat := 118140960795 + 2347668 * 2 ^ 59
def prefixEnd_2347668 : Nat := 4983230072969 + 3 ^ 40 * 2347668 * 2
def baseEnd_2347668 : Nat := 267884911373250215967395

theorem tailTrace_2347668 : CollatzResearch.WordTrace tailWord_2347668 prefixEnd_2347668 267884911373250215967395 := by
  unfold tailWord_2347668
  simp only [CollatzResearch.WordTrace]
  refine ⟨42813243229403630309133829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57084324305871507078845105 42813243229403630309133829)
  ·
    refine ⟨8027483105513180682962593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42813243229403630309133829 8027483105513180682962593)
    ·
      refine ⟨6020612329134885512221945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8027483105513180682962593 6020612329134885512221945)
      ·
        refine ⟨4515459246851164134166459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6020612329134885512221945 4515459246851164134166459)
        ·
          refine ⟨6773188870276746201249689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4515459246851164134166459 6773188870276746201249689)
          ·
            refine ⟨5079891652707559650937267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6773188870276746201249689 5079891652707559650937267)
            ·
              refine ⟨7619837479061339476405901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5079891652707559650937267 7619837479061339476405901)
              ·
                refine ⟨2857439054648002303652213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7619837479061339476405901 2857439054648002303652213)
                ·
                  refine ⟨267884911373250215967395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2857439054648002303652213 267884911373250215967395)
                  ·
                    rfl

theorem cell22_2347668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_2347668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347668 prefixEnd_2347668 := by exact prefixLift 2347668
  have htrace : WordTrace (prefixWord ++ tailWord_2347668) baseStart_2347668 baseEnd_2347668 := by
    simpa [prefixWord, tailWord_2347668, baseEnd_2347668] using wordTrace_append hprefix tailTrace_2347668
  have hstable : (prefixWord ++ tailWord_2347668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347668).length < 2 ^ (prefixWord ++ tailWord_2347668).sum := by decide
  have hdescent : baseEnd_2347668 < baseStart_2347668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347696 : List Nat := [2, 1, 1, 1, 2, 1, 3, 7, 4]
def baseStart_2347696 : Nat := 118140960795 + 2347696 * 2 ^ 59
def prefixEnd_2347696 : Nat := 4983230072969 + 3 ^ 40 * 2347696 * 2
def baseEnd_2347696 : Nat := 267888106363989302734033

theorem tailTrace_2347696 : CollatzResearch.WordTrace tailWord_2347696 prefixEnd_2347696 267888106363989302734033 := by
  unfold tailWord_2347696
  simp only [CollatzResearch.WordTrace]
  refine ⟨42813753851352910700143471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57085005135137214266857961 42813753851352910700143471)
  ·
    refine ⟨64220630777029366050215207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42813753851352910700143471 64220630777029366050215207)
    ·
      refine ⟨96330946165544049075322811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64220630777029366050215207 96330946165544049075322811)
      ·
        refine ⟨144496419248316073612984217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96330946165544049075322811 144496419248316073612984217)
        ·
          refine ⟨108372314436237055209738163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144496419248316073612984217 108372314436237055209738163)
          ·
            refine ⟨162558471654355582814607245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108372314436237055209738163 162558471654355582814607245)
            ·
              refine ⟨60959426870383343555477717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162558471654355582814607245 60959426870383343555477717)
              ·
                refine ⟨1428736567274609614581509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60959426870383343555477717 1428736567274609614581509)
                ·
                  refine ⟨267888106363989302734033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1428736567274609614581509 267888106363989302734033)
                  ·
                    rfl

theorem cell22_2347696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 4].length) (baseStart_2347696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347696 prefixEnd_2347696 := by exact prefixLift 2347696
  have htrace : WordTrace (prefixWord ++ tailWord_2347696) baseStart_2347696 baseEnd_2347696 := by
    simpa [prefixWord, tailWord_2347696, baseEnd_2347696] using wordTrace_append hprefix tailTrace_2347696
  have hstable : (prefixWord ++ tailWord_2347696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347696).length < 2 ^ (prefixWord ++ tailWord_2347696).sum := by decide
  have hdescent : baseEnd_2347696 < baseStart_2347696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347743 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 2, 4]
def baseStart_2347743 : Nat := 118140960795 + 2347743 * 2 ^ 59
def prefixEnd_2347743 : Nat := 4983230072969 + 3 ^ 40 * 2347743 * 2
def baseEnd_2347743 : Nat := 803680408152475452276955

theorem tailTrace_2347743 : CollatzResearch.WordTrace tailWord_2347743 prefixEnd_2347743 803680408152475452276955 := by
  unfold tailWord_2347743
  simp only [CollatzResearch.WordTrace]
  refine ⟨85629221933535548427247883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57086147955690365618165255 85629221933535548427247883)
  ·
    refine ⟨128443832900303322640871825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85629221933535548427247883 128443832900303322640871825)
    ·
      refine ⟨96332874675227491980653869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128443832900303322640871825 96332874675227491980653869)
      ·
        refine ⟨36124828003210309492745201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96332874675227491980653869 36124828003210309492745201)
        ·
          refine ⟨27093621002407732119558901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36124828003210309492745201 27093621002407732119558901)
          ·
            refine ⟨2540026968975724886208647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27093621002407732119558901 2540026968975724886208647)
            ·
              refine ⟨3810040453463587329312971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540026968975724886208647 3810040453463587329312971)
              ·
                refine ⟨5715060680195380993969457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810040453463587329312971 5715060680195380993969457)
                ·
                  refine ⟨4286295510146535745477093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5715060680195380993969457 4286295510146535745477093)
                  ·
                    refine ⟨803680408152475452276955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4286295510146535745477093 803680408152475452276955)
                    ·
                      rfl

theorem cell22_2347743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_2347743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347743 prefixEnd_2347743 := by exact prefixLift 2347743
  have htrace : WordTrace (prefixWord ++ tailWord_2347743) baseStart_2347743 baseEnd_2347743 := by
    simpa [prefixWord, tailWord_2347743, baseEnd_2347743] using wordTrace_append hprefix tailTrace_2347743
  have hstable : (prefixWord ++ tailWord_2347743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347743).length < 2 ^ (prefixWord ++ tailWord_2347743).sum := by decide
  have hdescent : baseEnd_2347743 < baseStart_2347743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347756 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_2347756 : Nat := 118140960795 + 2347756 * 2 ^ 59
def prefixEnd_2347756 : Nat := 4983230072969 + 3 ^ 40 * 2347756 * 2
def baseEnd_2347756 : Nat := 803684858318147751701915

theorem tailTrace_2347756 : CollatzResearch.WordTrace tailWord_2347756 prefixEnd_2347756 803684858318147751701915 := by
  unfold tailWord_2347756
  simp only [CollatzResearch.WordTrace]
  refine ⟨42814848041244225823735561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57086464054992301098314081 42814848041244225823735561)
  ·
    refine ⟨32111136030933169367801671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42814848041244225823735561 32111136030933169367801671)
    ·
      refine ⟨48166704046399754051702507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32111136030933169367801671 48166704046399754051702507)
      ·
        refine ⟨72250056069599631077553761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48166704046399754051702507 72250056069599631077553761)
        ·
          refine ⟨54187542052199723308165321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72250056069599631077553761 54187542052199723308165321)
          ·
            refine ⟨40640656539149792481123991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54187542052199723308165321 40640656539149792481123991)
            ·
              refine ⟨60960984808724688721685987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40640656539149792481123991 60960984808724688721685987)
              ·
                refine ⟨91441477213087033082528981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60960984808724688721685987 91441477213087033082528981)
                ·
                  refine ⟨2143159622181727337871773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 91441477213087033082528981 2143159622181727337871773)
                  ·
                    refine ⟨803684858318147751701915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143159622181727337871773 803684858318147751701915)
                    ·
                      rfl

theorem cell22_2347756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_2347756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347756 prefixEnd_2347756 := by exact prefixLift 2347756
  have htrace : WordTrace (prefixWord ++ tailWord_2347756) baseStart_2347756 baseEnd_2347756 := by
    simpa [prefixWord, tailWord_2347756, baseEnd_2347756] using wordTrace_append hprefix tailTrace_2347756
  have hstable : (prefixWord ++ tailWord_2347756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347756).length < 2 ^ (prefixWord ++ tailWord_2347756).sum := by decide
  have hdescent : baseEnd_2347756 < baseStart_2347756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347773 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_2347773 : Nat := 118140960795 + 2347773 * 2 ^ 59
def prefixEnd_2347773 : Nat := 4983230072969 + 3 ^ 40 * 2347773 * 2
def baseEnd_2347773 : Nat := 803690677765565374026863

theorem tailTrace_2347773 : CollatzResearch.WordTrace tailWord_2347773 prefixEnd_2347773 803690677765565374026863 := by
  unfold tailWord_2347773
  simp only [CollatzResearch.WordTrace]
  refine ⟨85630316123426863550839973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57086877415617909033893315 85630316123426863550839973)
  ·
    refine ⟨16055684273142536915782495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85630316123426863550839973 16055684273142536915782495)
    ·
      refine ⟨24083526409713805373673743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16055684273142536915782495 24083526409713805373673743)
      ·
        refine ⟨36125289614570708060510615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24083526409713805373673743 36125289614570708060510615)
        ·
          refine ⟨54187934421856062090765923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36125289614570708060510615 54187934421856062090765923)
          ·
            refine ⟨81281901632784093136148885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54187934421856062090765923 81281901632784093136148885)
            ·
              refine ⟨3810089139036754365756979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81281901632784093136148885 3810089139036754365756979)
              ·
                refine ⟨5715133708555131548635469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810089139036754365756979 5715133708555131548635469)
                ·
                  refine ⟨2143175140708174330738301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5715133708555131548635469 2143175140708174330738301)
                  ·
                    refine ⟨803690677765565374026863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143175140708174330738301 803690677765565374026863)
                    ·
                      rfl

theorem cell22_2347773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_2347773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347773 prefixEnd_2347773 := by exact prefixLift 2347773
  have htrace : WordTrace (prefixWord ++ tailWord_2347773) baseStart_2347773 baseEnd_2347773 := by
    simpa [prefixWord, tailWord_2347773, baseEnd_2347773] using wordTrace_append hprefix tailTrace_2347773
  have hstable : (prefixWord ++ tailWord_2347773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347773).length < 2 ^ (prefixWord ++ tailWord_2347773).sum := by decide
  have hdescent : baseEnd_2347773 < baseStart_2347773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347807 : List Nat := [1, 1, 2, 4, 2, 4, 1, 3, 1, 3]
def baseStart_2347807 : Nat := 118140960795 + 2347807 * 2 ^ 59
def prefixEnd_2347807 : Nat := 4983230072969 + 3 ^ 40 * 2347807 * 2
def baseEnd_2347807 : Nat := 803702316660400618676759

theorem tailTrace_2347807 : CollatzResearch.WordTrace tailWord_2347807 prefixEnd_2347807 803702316660400618676759 := by
  unfold tailWord_2347807
  simp only [CollatzResearch.WordTrace]
  refine ⟨85631556205303687357577675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57087704136869124905051783 85631556205303687357577675)
  ·
    refine ⟨128447334307955531036366513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85631556205303687357577675 128447334307955531036366513)
    ·
      refine ⟨96335500730966648277274885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128447334307955531036366513 96335500730966648277274885)
      ·
        refine ⟨18062906387056246551989041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96335500730966648277274885 18062906387056246551989041)
        ·
          refine ⟨13547179790292184913991781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18062906387056246551989041 13547179790292184913991781)
          ·
            refine ⟨2540096210679784671373459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13547179790292184913991781 2540096210679784671373459)
            ·
              refine ⟨3810144316019677007060189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540096210679784671373459 3810144316019677007060189)
              ·
                refine ⟨1428804118507378877647571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3810144316019677007060189 1428804118507378877647571)
                ·
                  refine ⟨2143206177761068316471357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428804118507378877647571 2143206177761068316471357)
                  ·
                    refine ⟨803702316660400618676759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143206177761068316471357 803702316660400618676759)
                    ·
                      rfl

theorem cell22_2347807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 1, 3].length) (baseStart_2347807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347807 prefixEnd_2347807 := by exact prefixLift 2347807
  have htrace : WordTrace (prefixWord ++ tailWord_2347807) baseStart_2347807 baseEnd_2347807 := by
    simpa [prefixWord, tailWord_2347807, baseEnd_2347807] using wordTrace_append hprefix tailTrace_2347807
  have hstable : (prefixWord ++ tailWord_2347807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347807).length < 2 ^ (prefixWord ++ tailWord_2347807).sum := by decide
  have hdescent : baseEnd_2347807 < baseStart_2347807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347837 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 5]
def baseStart_2347837 : Nat := 118140960795 + 2347837 * 2 ^ 59
def prefixEnd_2347837 : Nat := 4983230072969 + 3 ^ 40 * 2347837 * 2
def baseEnd_2347837 : Nat := 267904195424496846808889

theorem tailTrace_2347837 : CollatzResearch.WordTrace tailWord_2347837 prefixEnd_2347837 267904195424496846808889 := by
  unfold tailWord_2347837
  simp only [CollatzResearch.WordTrace]
  refine ⟨85632650395195002481169765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57088433596796668320779843 85632650395195002481169765)
  ·
    refine ⟨16056121949099062965219331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85632650395195002481169765 16056121949099062965219331)
    ·
      refine ⟨24084182923648594447828997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16056121949099062965219331 24084182923648594447828997)
      ·
        refine ⟨4515784298184111458967937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24084182923648594447828997 4515784298184111458967937)
        ·
          refine ⟨3386838223638083594225953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4515784298184111458967937 3386838223638083594225953)
          ·
            refine ⟨2540128667728562695669465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3386838223638083594225953 2540128667728562695669465)
            ·
              refine ⟨1905096500796422021752099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2540128667728562695669465 1905096500796422021752099)
              ·
                refine ⟨2857644751194633032628149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905096500796422021752099 2857644751194633032628149)
                ·
                  refine ⟨267904195424496846808889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2857644751194633032628149 267904195424496846808889)
                  ·
                    rfl

theorem cell22_2347837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_2347837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347837 prefixEnd_2347837 := by exact prefixLift 2347837
  have htrace : WordTrace (prefixWord ++ tailWord_2347837) baseStart_2347837 baseEnd_2347837 := by
    simpa [prefixWord, tailWord_2347837, baseEnd_2347837] using wordTrace_append hprefix tailTrace_2347837
  have hstable : (prefixWord ++ tailWord_2347837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347837).length < 2 ^ (prefixWord ++ tailWord_2347837).sum := by decide
  have hdescent : baseEnd_2347837 < baseStart_2347837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347863 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 1, 5]
def baseStart_2347863 : Nat := 118140960795 + 2347863 * 2 ^ 59
def prefixEnd_2347863 : Nat := 4983230072969 + 3 ^ 40 * 2347863 * 2
def baseEnd_2347863 : Nat := 803721486604835139276587

theorem tailTrace_2347863 : CollatzResearch.WordTrace tailWord_2347863 prefixEnd_2347863 803721486604835139276587 := by
  unfold tailWord_2347863
  simp only [CollatzResearch.WordTrace]
  refine ⟨85633598693100808921616243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57089065795400539281077495 85633598693100808921616243)
  ·
    refine ⟨128450398039651213382424365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85633598693100808921616243 128450398039651213382424365)
    ·
      refine ⟨48168899264869205018409137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128450398039651213382424365 48168899264869205018409137)
      ·
        refine ⟨36126674448651903763806853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48168899264869205018409137 36126674448651903763806853)
        ·
          refine ⟨6773751459122231955713785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36126674448651903763806853 6773751459122231955713785)
          ·
            refine ⟨5080313594341673966785339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6773751459122231955713785 5080313594341673966785339)
            ·
              refine ⟨7620470391512510950178009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5080313594341673966785339 7620470391512510950178009)
              ·
                refine ⟨5715352793634383212633507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7620470391512510950178009 5715352793634383212633507)
                ·
                  refine ⟨8573029190451574818950261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5715352793634383212633507 8573029190451574818950261)
                  ·
                    refine ⟨803721486604835139276587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8573029190451574818950261 803721486604835139276587)
                    ·
                      rfl

theorem cell22_2347863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_2347863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347863 prefixEnd_2347863 := by exact prefixLift 2347863
  have htrace : WordTrace (prefixWord ++ tailWord_2347863) baseStart_2347863 baseEnd_2347863 := by
    simpa [prefixWord, tailWord_2347863, baseEnd_2347863] using wordTrace_append hprefix tailTrace_2347863
  have hstable : (prefixWord ++ tailWord_2347863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347863).length < 2 ^ (prefixWord ++ tailWord_2347863).sum := by decide
  have hdescent : baseEnd_2347863 < baseStart_2347863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347876 : List Nat := [2, 3, 1, 1, 4, 11]
def baseStart_2347876 : Nat := 118140960795 + 2347876 * 2 ^ 59
def prefixEnd_2347876 : Nat := 4983230072969 + 3 ^ 40 * 2347876 * 2
def baseEnd_2347876 : Nat := 9922542429265523934587

theorem tailTrace_2347876 : CollatzResearch.WordTrace tailWord_2347876 prefixEnd_2347876 9922542429265523934587 := by
  unfold tailWord_2347876
  simp only [CollatzResearch.WordTrace]
  refine ⟨42817036421026856070919741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57089381894702474761226321 42817036421026856070919741)
  ·
    refine ⟨16056388657885071026594903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42817036421026856070919741 16056388657885071026594903)
    ·
      refine ⟨24084582986827606539892355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16056388657885071026594903 24084582986827606539892355)
      ·
        refine ⟨36126874480241409809838533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24084582986827606539892355 36126874480241409809838533)
        ·
          refine ⟨6773788965045264339344725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36126874480241409809838533 6773788965045264339344725)
          ·
            refine ⟨9922542429265523934587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6773788965045264339344725 9922542429265523934587)
            ·
              rfl

theorem cell22_2347876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 11].length) (baseStart_2347876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347876 prefixEnd_2347876 := by exact prefixLift 2347876
  have htrace : WordTrace (prefixWord ++ tailWord_2347876) baseStart_2347876 baseEnd_2347876 := by
    simpa [prefixWord, tailWord_2347876, baseEnd_2347876] using wordTrace_append hprefix tailTrace_2347876
  have hstable : (prefixWord ++ tailWord_2347876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347876).length < 2 ^ (prefixWord ++ tailWord_2347876).sum := by decide
  have hdescent : baseEnd_2347876 < baseStart_2347876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347880 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 2, 3]
def baseStart_2347880 : Nat := 118140960795 + 2347880 * 2 ^ 59
def prefixEnd_2347880 : Nat := 4983230072969 + 3 ^ 40 * 2347880 * 2
def baseEnd_2347880 : Nat := 803727306052252761601535

theorem tailTrace_2347880 : CollatzResearch.WordTrace tailWord_2347880 prefixEnd_2347880 803727306052252761601535 := by
  unfold tailWord_2347880
  simp only [CollatzResearch.WordTrace]
  refine ⟨42817109367019610412492547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57089479156026147216656729 42817109367019610412492547)
  ·
    refine ⟨64225664050529415618738821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42817109367019610412492547 64225664050529415618738821)
    ·
      refine ⟨12042312009474265428513529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64225664050529415618738821 12042312009474265428513529)
      ·
        refine ⟨9031734007105699071385147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12042312009474265428513529 9031734007105699071385147)
        ·
          refine ⟨13547601010658548607077721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9031734007105699071385147 13547601010658548607077721)
          ·
            refine ⟨10160700757993911455308291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13547601010658548607077721 10160700757993911455308291)
            ·
              refine ⟨15241051136990867182962437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10160700757993911455308291 15241051136990867182962437)
              ·
                refine ⟨2857697088185787596805457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15241051136990867182962437 2857697088185787596805457)
                ·
                  refine ⟨2143272816139340697604093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2857697088185787596805457 2143272816139340697604093)
                  ·
                    refine ⟨803727306052252761601535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143272816139340697604093 803727306052252761601535)
                    ·
                      rfl

theorem cell22_2347880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_2347880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347880 prefixEnd_2347880 := by exact prefixLift 2347880
  have htrace : WordTrace (prefixWord ++ tailWord_2347880) baseStart_2347880 baseEnd_2347880 := by
    simpa [prefixWord, tailWord_2347880, baseEnd_2347880] using wordTrace_append hprefix tailTrace_2347880
  have hstable : (prefixWord ++ tailWord_2347880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347880).length < 2 ^ (prefixWord ++ tailWord_2347880).sum := by decide
  have hdescent : baseEnd_2347880 < baseStart_2347880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347893 : List Nat := [1, 3, 4, 1, 1, 2, 3, 7]
def baseStart_2347893 : Nat := 118140960795 + 2347893 * 2 ^ 59
def prefixEnd_2347893 : Nat := 4983230072969 + 3 ^ 40 * 2347893 * 2
def baseEnd_2347893 : Nat := 89303528468658340114055

theorem tailTrace_2347893 : CollatzResearch.WordTrace tailWord_2347893 prefixEnd_2347893 89303528468658340114055 := by
  unfold tailWord_2347893
  simp only [CollatzResearch.WordTrace]
  refine ⟨85634692882992124045208333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57089795255328082696805555 85634692882992124045208333)
  ·
    refine ⟨32113009831122046516953125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85634692882992124045208333 32113009831122046516953125)
    ·
      refine ⟨6021189343335383721928711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32113009831122046516953125 6021189343335383721928711)
      ·
        refine ⟨9031784015003075582893067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6021189343335383721928711 9031784015003075582893067)
        ·
          refine ⟨13547676022504613374339601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9031784015003075582893067 13547676022504613374339601)
          ·
            refine ⟨10160757016878460030754701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13547676022504613374339601 10160757016878460030754701)
            ·
              refine ⟨3810283881329422511533013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10160757016878460030754701 3810283881329422511533013)
              ·
                refine ⟨89303528468658340114055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3810283881329422511533013 89303528468658340114055)
                ·
                  rfl

theorem cell22_2347893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 7].length) (baseStart_2347893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347893 prefixEnd_2347893 := by exact prefixLift 2347893
  have htrace : WordTrace (prefixWord ++ tailWord_2347893) baseStart_2347893 baseEnd_2347893 := by
    simpa [prefixWord, tailWord_2347893, baseEnd_2347893] using wordTrace_append hprefix tailTrace_2347893
  have hstable : (prefixWord ++ tailWord_2347893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347893).length < 2 ^ (prefixWord ++ tailWord_2347893).sum := by decide
  have hdescent : baseEnd_2347893 < baseStart_2347893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347921 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 7]
def baseStart_2347921 : Nat := 118140960795 + 2347921 * 2 ^ 59
def prefixEnd_2347921 : Nat := 4983230072969 + 3 ^ 40 * 2347921 * 2
def baseEnd_2347921 : Nat := 267913780396714107108803

theorem tailTrace_2347921 : CollatzResearch.WordTrace tailWord_2347921 prefixEnd_2347921 267913780396714107108803 := by
  unfold tailWord_2347921
  simp only [CollatzResearch.WordTrace]
  refine ⟨85635714126890684827227617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57090476084593789884818411 85635714126890684827227617)
  ·
    refine ⟨64226785595168013620420713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85635714126890684827227617 64226785595168013620420713)
    ·
      refine ⟨48170089196376010215315535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64226785595168013620420713 48170089196376010215315535)
      ·
        refine ⟨72255133794564015322973303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48170089196376010215315535 72255133794564015322973303)
        ·
          refine ⟨108382700691846022984459955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72255133794564015322973303 108382700691846022984459955)
          ·
            refine ⟨162574051037769034476689933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108382700691846022984459955 162574051037769034476689933)
            ·
              refine ⟨60965269139163387928758725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162574051037769034476689933 60965269139163387928758725)
              ·
                refine ⟨11430987963593135236642261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60965269139163387928758725 11430987963593135236642261)
                ·
                  refine ⟨267913780396714107108803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11430987963593135236642261 267913780396714107108803)
                  ·
                    rfl

theorem cell22_2347921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_2347921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347921 prefixEnd_2347921 := by exact prefixLift 2347921
  have htrace : WordTrace (prefixWord ++ tailWord_2347921) baseStart_2347921 baseEnd_2347921 := by
    simpa [prefixWord, tailWord_2347921, baseEnd_2347921] using wordTrace_append hprefix tailTrace_2347921
  have hstable : (prefixWord ++ tailWord_2347921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347921).length < 2 ^ (prefixWord ++ tailWord_2347921).sum := by decide
  have hdescent : baseEnd_2347921 < baseStart_2347921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347951 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 2, 8]
def baseStart_2347951 : Nat := 118140960795 + 2347951 * 2 ^ 59
def prefixEnd_2347951 : Nat := 4983230072969 + 3 ^ 40 * 2347951 * 2
def baseEnd_2347951 : Nat := 803751610803232243076317

theorem tailTrace_2347951 : CollatzResearch.WordTrace tailWord_2347951 prefixEnd_2347951 803751610803232243076317 := by
  unfold tailWord_2347951
  simp only [CollatzResearch.WordTrace]
  refine ⟨85636808316781999950819707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57091205544521333300546471 85636808316781999950819707)
  ·
    refine ⟨128455212475172999926229561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85636808316781999950819707 128455212475172999926229561)
    ·
      refine ⟨96341409356379749944672171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128455212475172999926229561 96341409356379749944672171)
      ·
        refine ⟨144512114034569624917008257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96341409356379749944672171 144512114034569624917008257)
        ·
          refine ⟨108384085525927218687756193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144512114034569624917008257 108384085525927218687756193)
          ·
            refine ⟨81288064144445414015817145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108384085525927218687756193 81288064144445414015817145)
            ·
              refine ⟨60966048108334060511862859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81288064144445414015817145 60966048108334060511862859)
              ·
                refine ⟨91449072162501090767794289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60966048108334060511862859 91449072162501090767794289)
                ·
                  refine ⟨68586804121875818075845717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91449072162501090767794289 68586804121875818075845717)
                  ·
                    refine ⟨803751610803232243076317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68586804121875818075845717 803751610803232243076317)
                    ·
                      rfl

theorem cell22_2347951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_2347951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347951 prefixEnd_2347951 := by exact prefixLift 2347951
  have htrace : WordTrace (prefixWord ++ tailWord_2347951) baseStart_2347951 baseEnd_2347951 := by
    simpa [prefixWord, tailWord_2347951, baseEnd_2347951] using wordTrace_append hprefix tailTrace_2347951
  have hstable : (prefixWord ++ tailWord_2347951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347951).length < 2 ^ (prefixWord ++ tailWord_2347951).sum := by decide
  have hdescent : baseEnd_2347951 < baseStart_2347951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2347976 : List Nat := [2, 1, 3, 1, 6, 1, 1, 3, 1, 3]
def baseStart_2347976 : Nat := 118140960795 + 2347976 * 2 ^ 59
def prefixEnd_2347976 : Nat := 4983230072969 + 3 ^ 40 * 2347976 * 2
def baseEnd_2347976 : Nat := 803760168814140511201241

theorem tailTrace_2347976 : CollatzResearch.WordTrace tailWord_2347976 prefixEnd_2347976 803760168814140511201241 := by
  unfold tailWord_2347976
  simp only [CollatzResearch.WordTrace]
  refine ⟨42818860070845714610239891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57091813427794286146986521 42818860070845714610239891)
  ·
    refine ⟨64228290106268571915359837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42818860070845714610239891 64228290106268571915359837)
    ·
      refine ⟨24085608789850714468259939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64228290106268571915359837 24085608789850714468259939)
      ·
        refine ⟨36128413184776071702389909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24085608789850714468259939 36128413184776071702389909)
        ·
          refine ⟨1693519368036378361049527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36128413184776071702389909 1693519368036378361049527)
          ·
            refine ⟨2540279052054567541574291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693519368036378361049527 2540279052054567541574291)
            ·
              refine ⟨3810418578081851312361437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2540279052054567541574291 3810418578081851312361437)
              ·
                refine ⟨1428906966780694242135539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3810418578081851312361437 1428906966780694242135539)
                ·
                  refine ⟨2143360450171041363203309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1428906966780694242135539 2143360450171041363203309)
                  ·
                    refine ⟨803760168814140511201241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143360450171041363203309 803760168814140511201241)
                    ·
                      rfl

theorem cell22_2347976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_2347976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2347976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2347976 prefixEnd_2347976 := by exact prefixLift 2347976
  have htrace : WordTrace (prefixWord ++ tailWord_2347976) baseStart_2347976 baseEnd_2347976 := by
    simpa [prefixWord, tailWord_2347976, baseEnd_2347976] using wordTrace_append hprefix tailTrace_2347976
  have hstable : (prefixWord ++ tailWord_2347976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2347976).length < 2 ^ (prefixWord ++ tailWord_2347976).sum := by decide
  have hdescent : baseEnd_2347976 < baseStart_2347976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2347976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348028 : List Nat := [2, 2, 2, 1, 2, 3, 2, 8]
def baseStart_2348028 : Nat := 118140960795 + 2348028 * 2 ^ 59
def prefixEnd_2348028 : Nat := 4983230072969 + 3 ^ 40 * 2348028 * 2
def baseEnd_2348028 : Nat := 89308663275203300989009

theorem tailTrace_2348028 : CollatzResearch.WordTrace tailWord_2348028 prefixEnd_2348028 89308663275203300989009 := by
  unfold tailWord_2348028
  simp only [CollatzResearch.WordTrace]
  refine ⟨42819808368751521050686369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57093077825002028067581825 42819808368751521050686369)
  ·
    refine ⟨32114856276563640788014777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42819808368751521050686369 32114856276563640788014777)
    ·
      refine ⟨24086142207422730591011083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32114856276563640788014777 24086142207422730591011083)
      ·
        refine ⟨36129213311134095886516625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24086142207422730591011083 36129213311134095886516625)
        ·
          refine ⟨27096909983350571914887469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36129213311134095886516625 27096909983350571914887469)
          ·
            refine ⟨10161341243756464468082801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27096909983350571914887469 10161341243756464468082801)
            ·
              refine ⟨7621005932817348351062101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10161341243756464468082801 7621005932817348351062101)
              ·
                refine ⟨89308663275203300989009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7621005932817348351062101 89308663275203300989009)
                ·
                  rfl

theorem cell22_2348028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 8].length) (baseStart_2348028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348028 prefixEnd_2348028 := by exact prefixLift 2348028
  have htrace : WordTrace (prefixWord ++ tailWord_2348028) baseStart_2348028 baseEnd_2348028 := by
    simpa [prefixWord, tailWord_2348028, baseEnd_2348028] using wordTrace_append hprefix tailTrace_2348028
  have hstable : (prefixWord ++ tailWord_2348028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348028).length < 2 ^ (prefixWord ++ tailWord_2348028).sum := by decide
  have hdescent : baseEnd_2348028 < baseStart_2348028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348045 : List Nat := [1, 7, 1, 13]
def baseStart_2348045 : Nat := 118140960795 + 2348045 * 2 ^ 59
def prefixEnd_2348045 : Nat := 4983230072969 + 3 ^ 40 * 2348045 * 2
def baseEnd_2348045 : Nat := 1102584072598418835701

theorem tailTrace_2348045 : CollatzResearch.WordTrace tailWord_2348045 prefixEnd_2348045 1102584072598418835701 := by
  unfold tailWord_2348045
  simp only [CollatzResearch.WordTrace]
  refine ⟨85640236778441454004741589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57093491185627636003161059 85640236778441454004741589)
  ·
    refine ⟨2007193049494721578236131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 85640236778441454004741589 2007193049494721578236131)
    ·
      refine ⟨3010789574242082367354197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2007193049494721578236131 3010789574242082367354197)
      ·
        refine ⟨1102584072598418835701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3010789574242082367354197 1102584072598418835701)
        ·
          rfl

theorem cell22_2348045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 13].length) (baseStart_2348045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348045 prefixEnd_2348045 := by exact prefixLift 2348045
  have htrace : WordTrace (prefixWord ++ tailWord_2348045) baseStart_2348045 baseEnd_2348045 := by
    simpa [prefixWord, tailWord_2348045, baseEnd_2348045] using wordTrace_append hprefix tailTrace_2348045
  have hstable : (prefixWord ++ tailWord_2348045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348045).length < 2 ^ (prefixWord ++ tailWord_2348045).sum := by decide
  have hdescent : baseEnd_2348045 < baseStart_2348045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348058 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_2348058 : Nat := 118140960795 + 2348058 * 2 ^ 59
def prefixEnd_2348058 : Nat := 4983230072969 + 3 ^ 40 * 2348058 * 2
def baseEnd_2348058 : Nat := 803788239089919630650989

theorem tailTrace_2348058 : CollatzResearch.WordTrace tailWord_2348058 prefixEnd_2348058 803788239089919630650989 := by
  unfold tailWord_2348058
  simp only [CollatzResearch.WordTrace]
  refine ⟨21410177731848589306241207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57093807284929571483309885 21410177731848589306241207)
  ·
    refine ⟨32115266597772883959361811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21410177731848589306241207 32115266597772883959361811)
    ·
      refine ⟨48172899896659325939042717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32115266597772883959361811 48172899896659325939042717)
      ·
        refine ⟨18064837461247247227141019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48172899896659325939042717 18064837461247247227141019)
        ·
          refine ⟨27097256191870870840711529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18064837461247247227141019 27097256191870870840711529)
          ·
            refine ⟨20322942143903153130533647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27097256191870870840711529 20322942143903153130533647)
            ·
              refine ⟨30484413215854729695800471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20322942143903153130533647 30484413215854729695800471)
              ·
                refine ⟨45726619823782094543700707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30484413215854729695800471 45726619823782094543700707)
                ·
                  refine ⟨68589929735673141815551061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45726619823782094543700707 68589929735673141815551061)
                  ·
                    refine ⟨803788239089919630650989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68589929735673141815551061 803788239089919630650989)
                    ·
                      rfl

theorem cell22_2348058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_2348058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348058 prefixEnd_2348058 := by exact prefixLift 2348058
  have htrace : WordTrace (prefixWord ++ tailWord_2348058) baseStart_2348058 baseEnd_2348058 := by
    simpa [prefixWord, tailWord_2348058, baseEnd_2348058] using wordTrace_append hprefix tailTrace_2348058
  have hstable : (prefixWord ++ tailWord_2348058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348058).length < 2 ^ (prefixWord ++ tailWord_2348058).sum := by decide
  have hdescent : baseEnd_2348058 < baseStart_2348058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348135 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 6]
def baseStart_2348135 : Nat := 118140960795 + 2348135 * 2 ^ 59
def prefixEnd_2348135 : Nat := 4983230072969 + 3 ^ 40 * 2348135 * 2
def baseEnd_2348135 : Nat := 267938199254505698825251

theorem tailTrace_2348135 : CollatzResearch.WordTrace tailWord_2348135 prefixEnd_2348135 267938199254505698825251 := by
  unfold tailWord_2348135
  simp only [CollatzResearch.WordTrace]
  refine ⟨85643519348115399375517859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57095679565410266250345239 85643519348115399375517859)
  ·
    refine ⟨128465279022173099063276789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85643519348115399375517859 128465279022173099063276789)
    ·
      refine ⟨12043619908328728037182199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128465279022173099063276789 12043619908328728037182199)
      ·
        refine ⟨18065429862493092055773299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12043619908328728037182199 18065429862493092055773299)
        ·
          refine ⟨27098144793739638083659949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18065429862493092055773299 27098144793739638083659949)
          ·
            refine ⟨10161804297652364281372481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27098144793739638083659949 10161804297652364281372481)
            ·
              refine ⟨7621353223239273211029361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10161804297652364281372481 7621353223239273211029361)
              ·
                refine ⟨5716014917429454908272021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7621353223239273211029361 5716014917429454908272021)
                ·
                  refine ⟨267938199254505698825251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5716014917429454908272021 267938199254505698825251)
                  ·
                    rfl

theorem cell22_2348135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 6].length) (baseStart_2348135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348135 prefixEnd_2348135 := by exact prefixLift 2348135
  have htrace : WordTrace (prefixWord ++ tailWord_2348135) baseStart_2348135 baseEnd_2348135 := by
    simpa [prefixWord, tailWord_2348135, baseEnd_2348135] using wordTrace_append hprefix tailTrace_2348135
  have hstable : (prefixWord ++ tailWord_2348135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348135).length < 2 ^ (prefixWord ++ tailWord_2348135).sum := by decide
  have hdescent : baseEnd_2348135 < baseStart_2348135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348137 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_2348137 : Nat := 118140960795 + 2348137 * 2 ^ 59
def prefixEnd_2348137 : Nat := 4983230072969 + 3 ^ 40 * 2348137 * 2
def baseEnd_2348137 : Nat := 803815282404389757925747

theorem tailTrace_2348137 : CollatzResearch.WordTrace tailWord_2348137 prefixEnd_2348137 803815282404389757925747 := by
  unfold tailWord_2348137
  simp only [CollatzResearch.WordTrace]
  refine ⟨85643592294108153717090665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57095728196072102478060443 85643592294108153717090665)
  ·
    refine ⟨64232694220581115287817999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85643592294108153717090665 64232694220581115287817999)
    ·
      refine ⟨96349041330871672931726999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64232694220581115287817999 96349041330871672931726999)
      ·
        refine ⟨144523561996307509397590499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96349041330871672931726999 144523561996307509397590499)
        ·
          refine ⟨216785342994461264096385749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144523561996307509397590499 216785342994461264096385749)
          ·
            refine ⟨5080906476432685877259041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 216785342994461264096385749 5080906476432685877259041)
            ·
              refine ⟨3810679857324514407944281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5080906476432685877259041 3810679857324514407944281)
              ·
                refine ⟨2858009892993385805958211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3810679857324514407944281 2858009892993385805958211)
                ·
                  refine ⟨4287014839490078708937317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858009892993385805958211 4287014839490078708937317)
                  ·
                    refine ⟨803815282404389757925747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287014839490078708937317 803815282404389757925747)
                    ·
                      rfl

theorem cell22_2348137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_2348137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348137 prefixEnd_2348137 := by exact prefixLift 2348137
  have htrace : WordTrace (prefixWord ++ tailWord_2348137) baseStart_2348137 baseEnd_2348137 := by
    simpa [prefixWord, tailWord_2348137, baseEnd_2348137] using wordTrace_append hprefix tailTrace_2348137
  have hstable : (prefixWord ++ tailWord_2348137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348137).length < 2 ^ (prefixWord ++ tailWord_2348137).sum := by decide
  have hdescent : baseEnd_2348137 < baseStart_2348137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348152 : List Nat := [2, 1, 2, 1, 1, 1, 7, 3, 4]
def baseStart_2348152 : Nat := 118140960795 + 2348152 * 2 ^ 59
def prefixEnd_2348152 : Nat := 4983230072969 + 3 ^ 40 * 2348152 * 2
def baseEnd_2348152 : Nat := 267940139070311572933567

theorem tailTrace_2348152 : CollatzResearch.WordTrace tailWord_2348152 prefixEnd_2348152 267940139070311572933567 := by
  unfold tailWord_2348152
  simp only [CollatzResearch.WordTrace]
  refine ⟨42822069694526905639443355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57096092926035874185924473 42822069694526905639443355)
  ·
    refine ⟨64233104541790358459165033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42822069694526905639443355 64233104541790358459165033)
    ·
      refine ⟨48174828406342768844373775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64233104541790358459165033 48174828406342768844373775)
      ·
        refine ⟨72262242609514153266560663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48174828406342768844373775 72262242609514153266560663)
        ·
          refine ⟨108393363914271229899840995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72262242609514153266560663 108393363914271229899840995)
          ·
            refine ⟨162590045871406844849761493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108393363914271229899840995 162590045871406844849761493)
            ·
              refine ⟨3810704200111097926166285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 162590045871406844849761493 3810704200111097926166285)
              ·
                refine ⟨1429014075041661722312357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3810704200111097926166285 1429014075041661722312357)
                ·
                  refine ⟨267940139070311572933567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1429014075041661722312357 267940139070311572933567)
                  ·
                    rfl

theorem cell22_2348152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 4].length) (baseStart_2348152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348152 prefixEnd_2348152 := by exact prefixLift 2348152
  have htrace : WordTrace (prefixWord ++ tailWord_2348152) baseStart_2348152 baseEnd_2348152 := by
    simpa [prefixWord, tailWord_2348152, baseEnd_2348152] using wordTrace_append hprefix tailTrace_2348152
  have hstable : (prefixWord ++ tailWord_2348152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348152).length < 2 ^ (prefixWord ++ tailWord_2348152).sum := by decide
  have hdescent : baseEnd_2348152 < baseStart_2348152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348167 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 2, 3]
def baseStart_2348167 : Nat := 118140960795 + 2348167 * 2 ^ 59
def prefixEnd_2348167 : Nat := 4983230072969 + 3 ^ 40 * 2348167 * 2
def baseEnd_2348167 : Nat := 803825552017479679675655

theorem tailTrace_2348167 : CollatzResearch.WordTrace tailWord_2348167 prefixEnd_2348167 803825552017479679675655 := by
  unfold tailWord_2348167
  simp only [CollatzResearch.WordTrace]
  refine ⟨85644686483999468840682755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57096457655999645893788503 85644686483999468840682755)
  ·
    refine ⟨128467029725999203261024133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85644686483999468840682755 128467029725999203261024133)
    ·
      refine ⟨24087568073624850611442025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128467029725999203261024133 24087568073624850611442025)
      ·
        refine ⟨18065676055218637958581519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24087568073624850611442025 18065676055218637958581519)
        ·
          refine ⟨27098514082827956937872279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18065676055218637958581519 27098514082827956937872279)
          ·
            refine ⟨40647771124241935406808419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27098514082827956937872279 40647771124241935406808419)
            ·
              refine ⟨60971656686362903110212629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40647771124241935406808419 60971656686362903110212629)
              ·
                refine ⟨2858046407173261083291217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60971656686362903110212629 2858046407173261083291217)
                ·
                  refine ⟨2143534805379945812468413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2858046407173261083291217 2143534805379945812468413)
                  ·
                    refine ⟨803825552017479679675655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143534805379945812468413 803825552017479679675655)
                    ·
                      rfl

theorem cell22_2348167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2348167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348167 prefixEnd_2348167 := by exact prefixLift 2348167
  have htrace : WordTrace (prefixWord ++ tailWord_2348167) baseStart_2348167 baseEnd_2348167 := by
    simpa [prefixWord, tailWord_2348167, baseEnd_2348167] using wordTrace_append hprefix tailTrace_2348167
  have hstable : (prefixWord ++ tailWord_2348167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348167).length < 2 ^ (prefixWord ++ tailWord_2348167).sum := by decide
  have hdescent : baseEnd_2348167 < baseStart_2348167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348169 : List Nat := [1, 2, 1, 1, 4, 4, 3, 2, 4]
def baseStart_2348169 : Nat := 118140960795 + 2348169 * 2 ^ 59
def prefixEnd_2348169 : Nat := 4983230072969 + 3 ^ 40 * 2348169 * 2
def baseEnd_2348169 : Nat := 267942078886117447041883

theorem tailTrace_2348169 : CollatzResearch.WordTrace tailWord_2348169 prefixEnd_2348169 267942078886117447041883 := by
  unfold tailWord_2348169
  simp only [CollatzResearch.WordTrace]
  refine ⟨85644759429992223182255561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57096506286661482121503707 85644759429992223182255561)
  ·
    refine ⟨64233569572494167386691671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85644759429992223182255561 64233569572494167386691671)
    ·
      refine ⟨96350354358741251080037507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64233569572494167386691671 96350354358741251080037507)
      ·
        refine ⟨144525531538111876620056261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96350354358741251080037507 144525531538111876620056261)
        ·
          refine ⟨27098537163395976866260549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144525531538111876620056261 27098537163395976866260549)
          ·
            refine ⟨5080975718136745662423853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27098537163395976866260549 5080975718136745662423853)
            ·
              refine ⟨1905365894301279623408945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5080975718136745662423853 1905365894301279623408945)
              ·
                refine ⟨1429024420725959717556709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1905365894301279623408945 1429024420725959717556709)
                ·
                  refine ⟨267942078886117447041883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1429024420725959717556709 267942078886117447041883)
                  ·
                    rfl

theorem cell22_2348169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 4].length) (baseStart_2348169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348169 prefixEnd_2348169 := by exact prefixLift 2348169
  have htrace : WordTrace (prefixWord ++ tailWord_2348169) baseStart_2348169 baseEnd_2348169 := by
    simpa [prefixWord, tailWord_2348169, baseEnd_2348169] using wordTrace_append hprefix tailTrace_2348169
  have hstable : (prefixWord ++ tailWord_2348169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348169).length < 2 ^ (prefixWord ++ tailWord_2348169).sum := by decide
  have hdescent : baseEnd_2348169 < baseStart_2348169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348184 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 2, 3]
def baseStart_2348184 : Nat := 118140960795 + 2348184 * 2 ^ 59
def prefixEnd_2348184 : Nat := 4983230072969 + 3 ^ 40 * 2348184 * 2
def baseEnd_2348184 : Nat := 803831371464897302000603

theorem tailTrace_2348184 : CollatzResearch.WordTrace tailWord_2348184 prefixEnd_2348184 803831371464897302000603 := by
  unfold tailWord_2348184
  simp only [CollatzResearch.WordTrace]
  refine ⟨42822653262468940372025803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57096871016625253829367737 42822653262468940372025803)
  ·
    refine ⟨64233979893703410558038705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42822653262468940372025803 64233979893703410558038705)
    ·
      refine ⟨48175484920277557918529029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64233979893703410558038705 48175484920277557918529029)
      ·
        refine ⟨9032903422552042109724193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48175484920277557918529029 9032903422552042109724193)
        ·
          refine ⟨6774677566914031582293145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9032903422552042109724193 6774677566914031582293145)
          ·
            refine ⟨5081008175185523686719859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6774677566914031582293145 5081008175185523686719859)
            ·
              refine ⟨7621512262778285530079789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5081008175185523686719859 7621512262778285530079789)
              ·
                refine ⟨2858067098541857073779921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7621512262778285530079789 2858067098541857073779921)
                ·
                  refine ⟨2143550323906392805334941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2858067098541857073779921 2143550323906392805334941)
                  ·
                    refine ⟨803831371464897302000603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143550323906392805334941 803831371464897302000603)
                    ·
                      rfl

theorem cell22_2348184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_2348184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348184 prefixEnd_2348184 := by exact prefixLift 2348184
  have htrace : WordTrace (prefixWord ++ tailWord_2348184) baseStart_2348184 baseEnd_2348184 := by
    simpa [prefixWord, tailWord_2348184, baseEnd_2348184] using wordTrace_append hprefix tailTrace_2348184
  have hstable : (prefixWord ++ tailWord_2348184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348184).length < 2 ^ (prefixWord ++ tailWord_2348184).sum := by decide
  have hdescent : baseEnd_2348184 < baseStart_2348184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348199 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 2, 4]
def baseStart_2348199 : Nat := 118140960795 + 2348199 * 2 ^ 59
def prefixEnd_2348199 : Nat := 4983230072969 + 3 ^ 40 * 2348199 * 2
def baseEnd_2348199 : Nat := 803836506271442262875557

theorem tailTrace_2348199 : CollatzResearch.WordTrace tailWord_2348199 prefixEnd_2348199 803836506271442262875557 := by
  unfold tailWord_2348199
  simp only [CollatzResearch.WordTrace]
  refine ⟨85645853619883538305847651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57097235746589025537231767 85645853619883538305847651)
  ·
    refine ⟨128468780429825307458771477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85645853619883538305847651 128468780429825307458771477)
    ·
      refine ⟨6021974082648061287129913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128468780429825307458771477 6021974082648061287129913)
      ·
        refine ⟨4516480561986045965347435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6021974082648061287129913 4516480561986045965347435)
        ·
          refine ⟨6774720842979068948021153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4516480561986045965347435 6774720842979068948021153)
          ·
            refine ⟨5081040632234301711015865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6774720842979068948021153 5081040632234301711015865)
            ·
              refine ⟨3810780474175726283261899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5081040632234301711015865 3810780474175726283261899)
              ·
                refine ⟨5716170711263589424892849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810780474175726283261899 5716170711263589424892849)
                ·
                  refine ⟨4287128033447692068669637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5716170711263589424892849 4287128033447692068669637)
                  ·
                    refine ⟨803836506271442262875557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287128033447692068669637 803836506271442262875557)
                    ·
                      rfl

theorem cell22_2348199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_2348199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348199 prefixEnd_2348199 := by exact prefixLift 2348199
  have htrace : WordTrace (prefixWord ++ tailWord_2348199) baseStart_2348199 baseEnd_2348199 := by
    simpa [prefixWord, tailWord_2348199, baseEnd_2348199] using wordTrace_append hprefix tailTrace_2348199
  have hstable : (prefixWord ++ tailWord_2348199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348199).length < 2 ^ (prefixWord ++ tailWord_2348199).sum := by decide
  have hdescent : baseEnd_2348199 < baseStart_2348199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348214 : List Nat := [5, 1, 3, 2, 1, 10]
def baseStart_2348214 : Nat := 118140960795 + 2348214 * 2 ^ 59
def prefixEnd_2348214 : Nat := 4983230072969 + 3 ^ 40 * 2348214 * 2
def baseEnd_2348214 : Nat := 9923970877506015108031

theorem tailTrace_2348214 : CollatzResearch.WordTrace tailWord_2348214 prefixEnd_2348214 9923970877506015108031 := by
  unfold tailWord_2348214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5352900044676824741727731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57097600476552797245095797 5352900044676824741727731)
  ·
    refine ⟨8029350067015237112591597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5352900044676824741727731 8029350067015237112591597)
    ·
      refine ⟨3011006275130713917221849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8029350067015237112591597 3011006275130713917221849)
      ·
        refine ⟨2258254706348035437916387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3011006275130713917221849 2258254706348035437916387)
        ·
          refine ⟨3387382059522053156874581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2258254706348035437916387 3387382059522053156874581)
          ·
            refine ⟨9923970877506015108031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3387382059522053156874581 9923970877506015108031)
            ·
              rfl

theorem cell22_2348214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 10].length) (baseStart_2348214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348214 prefixEnd_2348214 := by exact prefixLift 2348214
  have htrace : WordTrace (prefixWord ++ tailWord_2348214) baseStart_2348214 baseEnd_2348214 := by
    simpa [prefixWord, tailWord_2348214, baseEnd_2348214] using wordTrace_append hprefix tailTrace_2348214
  have hstable : (prefixWord ++ tailWord_2348214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348214).length < 2 ^ (prefixWord ++ tailWord_2348214).sum := by decide
  have hdescent : baseEnd_2348214 < baseStart_2348214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348242 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_2348242 : Nat := 118140960795 + 2348242 * 2 ^ 59
def prefixEnd_2348242 : Nat := 4983230072969 + 3 ^ 40 * 2348242 * 2
def baseEnd_2348242 : Nat := 267950408683401494683475

theorem tailTrace_2348242 : CollatzResearch.WordTrace tailWord_2348242 prefixEnd_2348242 267950408683401494683475 := by
  unfold tailWord_2348242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21411855489681939162415745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57098281305818504433108653 21411855489681939162415745)
  ·
    refine ⟨16058891617261454371811809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21411855489681939162415745 16058891617261454371811809)
    ·
      refine ⟨12044168712946090778858857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16058891617261454371811809 12044168712946090778858857)
      ·
        refine ⟨9033126534709568084144143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12044168712946090778858857 9033126534709568084144143)
        ·
          refine ⟨13549689802064352126216215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9033126534709568084144143 13549689802064352126216215)
          ·
            refine ⟨20324534703096528189324323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13549689802064352126216215 20324534703096528189324323)
            ·
              refine ⟨30486802054644792283986485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20324534703096528189324323 30486802054644792283986485)
              ·
                refine ⟨2858137692622949276623733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30486802054644792283986485 2858137692622949276623733)
                ·
                  refine ⟨267950408683401494683475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2858137692622949276623733 267950408683401494683475)
                  ·
                    rfl

theorem cell22_2348242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_2348242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348242 prefixEnd_2348242 := by exact prefixLift 2348242
  have htrace : WordTrace (prefixWord ++ tailWord_2348242) baseStart_2348242 baseEnd_2348242 := by
    simpa [prefixWord, tailWord_2348242, baseEnd_2348242] using wordTrace_append hprefix tailTrace_2348242
  have hstable : (prefixWord ++ tailWord_2348242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348242).length < 2 ^ (prefixWord ++ tailWord_2348242).sum := by decide
  have hdescent : baseEnd_2348242 < baseStart_2348242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348263 : List Nat := [1, 1, 5, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2348263 : Nat := 118140960795 + 2348263 * 2 ^ 59
def prefixEnd_2348263 : Nat := 4983230072969 + 3 ^ 40 * 2348263 * 2
def baseEnd_2348263 : Nat := 803858414779367429275361

theorem tailTrace_2348263 : CollatzResearch.WordTrace tailWord_2348263 prefixEnd_2348263 803858414779367429275361 := by
  unfold tailWord_2348263
  simp only [CollatzResearch.WordTrace]
  refine ⟨85648187891651677236177443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57098791927767784824118295 85648187891651677236177443)
  ·
    refine ⟨128472281837477515854266165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85648187891651677236177443 128472281837477515854266165)
    ·
      refine ⟨12044276422263517111337453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128472281837477515854266165 12044276422263517111337453)
      ·
        refine ⟨4516603658348818916751545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12044276422263517111337453 4516603658348818916751545)
        ·
          refine ⟨3387452743761614187563659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4516603658348818916751545 3387452743761614187563659)
          ·
            refine ⟨5081179115642421281345489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3387452743761614187563659 5081179115642421281345489)
            ·
              refine ⟨3810884336731815961009117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5081179115642421281345489 3810884336731815961009117)
              ·
                refine ⟨1429081626274430985378419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3810884336731815961009117 1429081626274430985378419)
                ·
                  refine ⟨2143622439411646478067629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429081626274430985378419 2143622439411646478067629)
                  ·
                    refine ⟨803858414779367429275361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143622439411646478067629 803858414779367429275361)
                    ·
                      rfl

theorem cell22_2348263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2348263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348263 prefixEnd_2348263 := by exact prefixLift 2348263
  have htrace : WordTrace (prefixWord ++ tailWord_2348263) baseStart_2348263 baseEnd_2348263 := by
    simpa [prefixWord, tailWord_2348263, baseEnd_2348263] using wordTrace_append hprefix tailTrace_2348263
  have hstable : (prefixWord ++ tailWord_2348263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348263).length < 2 ^ (prefixWord ++ tailWord_2348263).sum := by decide
  have hdescent : baseEnd_2348263 < baseStart_2348263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348285 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_2348285 : Nat := 118140960795 + 2348285 * 2 ^ 59
def prefixEnd_2348285 : Nat := 4983230072969 + 3 ^ 40 * 2348285 * 2
def baseEnd_2348285 : Nat := 803865945828966705225293

theorem tailTrace_2348285 : CollatzResearch.WordTrace tailWord_2348285 prefixEnd_2348285 803865945828966705225293 := by
  unfold tailWord_2348285
  simp only [CollatzResearch.WordTrace]
  refine ⟨85648990297571974993478309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57099326865047983328985539 85648990297571974993478309)
  ·
    refine ⟨16059185680794745311277183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85648990297571974993478309 16059185680794745311277183)
    ·
      refine ⟨24088778521192117966915775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16059185680794745311277183 24088778521192117966915775)
      ·
        refine ⟨36133167781788176950373663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24088778521192117966915775 36133167781788176950373663)
        ·
          refine ⟨54199751672682265425560495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36133167781788176950373663 54199751672682265425560495)
          ·
            refine ⟨81299627509023398138340743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54199751672682265425560495 81299627509023398138340743)
            ·
              refine ⟨121949441263535097207511115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81299627509023398138340743 121949441263535097207511115)
              ·
                refine ⟨182924161895302645811266673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121949441263535097207511115 182924161895302645811266673)
                ·
                  refine ⟨137193121421476984358450005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182924161895302645811266673 137193121421476984358450005)
                  ·
                    refine ⟨803865945828966705225293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 137193121421476984358450005 803865945828966705225293)
                    ·
                      rfl

theorem cell22_2348285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_2348285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348285 prefixEnd_2348285 := by exact prefixLift 2348285
  have htrace : WordTrace (prefixWord ++ tailWord_2348285) baseStart_2348285 baseEnd_2348285 := by
    simpa [prefixWord, tailWord_2348285, baseEnd_2348285] using wordTrace_append hprefix tailTrace_2348285
  have hstable : (prefixWord ++ tailWord_2348285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348285).length < 2 ^ (prefixWord ++ tailWord_2348285).sum := by decide
  have hdescent : baseEnd_2348285 < baseStart_2348285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348287 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 6]
def baseStart_2348287 : Nat := 118140960795 + 2348287 * 2 ^ 59
def prefixEnd_2348287 : Nat := 4983230072969 + 3 ^ 40 * 2348287 * 2
def baseEnd_2348287 : Nat := 267955543489946455558429

theorem tailTrace_2348287 : CollatzResearch.WordTrace tailWord_2348287 prefixEnd_2348287 267955543489946455558429 := by
  unfold tailWord_2348287
  simp only [CollatzResearch.WordTrace]
  refine ⟨85649063243564729335051115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57099375495709819556700743 85649063243564729335051115)
  ·
    refine ⟨128473594865347094002576673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85649063243564729335051115 128473594865347094002576673)
    ·
      refine ⟨96355196149010320501932505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128473594865347094002576673 96355196149010320501932505)
      ·
        refine ⟨72266397111757740376449379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96355196149010320501932505 72266397111757740376449379)
        ·
          refine ⟨108399595667636610564674069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72266397111757740376449379 108399595667636610564674069)
          ·
            refine ⟨5081231046920466120219097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108399595667636610564674069 5081231046920466120219097)
            ·
              refine ⟨3810923285190349590164323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5081231046920466120219097 3810923285190349590164323)
              ·
                refine ⟨5716384927785524385246485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3810923285190349590164323 5716384927785524385246485)
                ·
                  refine ⟨267955543489946455558429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5716384927785524385246485 267955543489946455558429)
                  ·
                    rfl

theorem cell22_2348287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 6].length) (baseStart_2348287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348287 prefixEnd_2348287 := by exact prefixLift 2348287
  have htrace : WordTrace (prefixWord ++ tailWord_2348287) baseStart_2348287 baseEnd_2348287 := by
    simpa [prefixWord, tailWord_2348287, baseEnd_2348287] using wordTrace_append hprefix tailTrace_2348287
  have hstable : (prefixWord ++ tailWord_2348287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348287).length < 2 ^ (prefixWord ++ tailWord_2348287).sum := by decide
  have hdescent : baseEnd_2348287 < baseStart_2348287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348353 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2348353 : Nat := 118140960795 + 2348353 * 2 ^ 59
def prefixEnd_2348353 : Nat := 4983230072969 + 3 ^ 40 * 2348353 * 2
def baseEnd_2348353 : Nat := 803889223618637194525085

theorem tailTrace_2348353 : CollatzResearch.WordTrace tailWord_2348353 prefixEnd_2348353 803889223618637194525085 := by
  unfold tailWord_2348353
  simp only [CollatzResearch.WordTrace]
  refine ⟨85651470461325622606953713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57100980307550415071302475 85651470461325622606953713)
  ·
    refine ⟨64238602845994216955215285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85651470461325622606953713 64238602845994216955215285)
    ·
      refine ⟨6022369016811957839551433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64238602845994216955215285 6022369016811957839551433)
      ·
        refine ⟨4516776762608968379663575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6022369016811957839551433 4516776762608968379663575)
        ·
          refine ⟨6775165143913452569495363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4516776762608968379663575 6775165143913452569495363)
          ·
            refine ⟨10162747715870178854243045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775165143913452569495363 10162747715870178854243045)
            ·
              refine ⟨1905515196725658535170571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10162747715870178854243045 1905515196725658535170571)
              ·
                refine ⟨2858272795088487802755857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905515196725658535170571 2858272795088487802755857)
                ·
                  refine ⟨2143704596316365852066893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2858272795088487802755857 2143704596316365852066893)
                  ·
                    refine ⟨803889223618637194525085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143704596316365852066893 803889223618637194525085)
                    ·
                      rfl

theorem cell22_2348353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2348353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348353 prefixEnd_2348353 := by exact prefixLift 2348353
  have htrace : WordTrace (prefixWord ++ tailWord_2348353) baseStart_2348353 baseEnd_2348353 := by
    simpa [prefixWord, tailWord_2348353, baseEnd_2348353] using wordTrace_append hprefix tailTrace_2348353
  have hstable : (prefixWord ++ tailWord_2348353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348353).length < 2 ^ (prefixWord ++ tailWord_2348353).sum := by decide
  have hdescent : baseEnd_2348353 < baseStart_2348353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348407 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 5, 4]
def baseStart_2348407 : Nat := 118140960795 + 2348407 * 2 ^ 59
def prefixEnd_2348407 : Nat := 4983230072969 + 3 ^ 40 * 2348407 * 2
def baseEnd_2348407 : Nat := 803907708922199053674919

theorem tailTrace_2348407 : CollatzResearch.WordTrace tailWord_2348407 prefixEnd_2348407 803907708922199053674919 := by
  unfold tailWord_2348407
  simp only [CollatzResearch.WordTrace]
  refine ⟨85653440003129989829419475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57102293335419993219612983 85653440003129989829419475)
  ·
    refine ⟨128480160004694984744129213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85653440003129989829419475 128480160004694984744129213)
    ·
      refine ⟨48180060001760619279048455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128480160004694984744129213 48180060001760619279048455)
      ·
        refine ⟨72270090002640928918572683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48180060001760619279048455 72270090002640928918572683)
        ·
          refine ⟨108405135003961393377859025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72270090002640928918572683 108405135003961393377859025)
          ·
            refine ⟨81303851252971045033394269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108405135003961393377859025 81303851252971045033394269)
            ·
              refine ⟨30488944219864141887522851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81303851252971045033394269 30488944219864141887522851)
              ·
                refine ⟨45733416329796212831284277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30488944219864141887522851 45733416329796212831284277)
                ·
                  refine ⟨4287507780918394952932901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45733416329796212831284277 4287507780918394952932901)
                  ·
                    refine ⟨803907708922199053674919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287507780918394952932901 803907708922199053674919)
                    ·
                      rfl

theorem cell22_2348407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_2348407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348407 prefixEnd_2348407 := by exact prefixLift 2348407
  have htrace : WordTrace (prefixWord ++ tailWord_2348407) baseStart_2348407 baseEnd_2348407 := by
    simpa [prefixWord, tailWord_2348407, baseEnd_2348407] using wordTrace_append hprefix tailTrace_2348407
  have hstable : (prefixWord ++ tailWord_2348407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348407).length < 2 ^ (prefixWord ++ tailWord_2348407).sum := by decide
  have hdescent : baseEnd_2348407 < baseStart_2348407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348424 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_2348424 : Nat := 118140960795 + 2348424 * 2 ^ 59
def prefixEnd_2348424 : Nat := 4983230072969 + 3 ^ 40 * 2348424 * 2
def baseEnd_2348424 : Nat := 803913528369616675999867

theorem tailTrace_2348424 : CollatzResearch.WordTrace tailWord_2348424 prefixEnd_2348424 803913528369616675999867 := by
  unfold tailWord_2348424
  simp only [CollatzResearch.WordTrace]
  refine ⟨42827030022034200866394163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57102706696045601155192217 42827030022034200866394163)
  ·
    refine ⟨64240545033051301299591245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42827030022034200866394163 64240545033051301299591245)
    ·
      refine ⟨24090204387394237987346717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64240545033051301299591245 24090204387394237987346717)
      ·
        refine ⟨9033826645272839245255019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24090204387394237987346717 9033826645272839245255019)
        ·
          refine ⟨13550739967909258867882529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9033826645272839245255019 13550739967909258867882529)
          ·
            refine ⟨10163054975931944150911897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13550739967909258867882529 10163054975931944150911897)
            ·
              refine ⟨7622291231948958113183923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10163054975931944150911897 7622291231948958113183923)
              ·
                refine ⟨11433436847923437169775885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7622291231948958113183923 11433436847923437169775885)
                ·
                  refine ⟨4287538817971288938665957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11433436847923437169775885 4287538817971288938665957)
                  ·
                    refine ⟨803913528369616675999867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287538817971288938665957 803913528369616675999867)
                    ·
                      rfl

theorem cell22_2348424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_2348424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348424 prefixEnd_2348424 := by exact prefixLift 2348424
  have htrace : WordTrace (prefixWord ++ tailWord_2348424) baseStart_2348424 baseEnd_2348424 := by
    simpa [prefixWord, tailWord_2348424, baseEnd_2348424] using wordTrace_append hprefix tailTrace_2348424
  have hstable : (prefixWord ++ tailWord_2348424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348424).length < 2 ^ (prefixWord ++ tailWord_2348424).sum := by decide
  have hdescent : baseEnd_2348424 < baseStart_2348424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348441 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 1, 4]
def baseStart_2348441 : Nat := 118140960795 + 2348441 * 2 ^ 59
def prefixEnd_2348441 : Nat := 4983230072969 + 3 ^ 40 * 2348441 * 2
def baseEnd_2348441 : Nat := 803919347817034298324815

theorem tailTrace_2348441 : CollatzResearch.WordTrace tailWord_2348441 prefixEnd_2348441 803919347817034298324815 := by
  unfold tailWord_2348441
  simp only [CollatzResearch.WordTrace]
  refine ⟨85654680085006813636157177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57103120056671209090771451 85654680085006813636157177)
  ·
    refine ⟨64241010063755110227117883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85654680085006813636157177 64241010063755110227117883)
    ·
      refine ⟨96361515095632665340676825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64241010063755110227117883 96361515095632665340676825)
      ·
        refine ⟨72271136321724499005507619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96361515095632665340676825 72271136321724499005507619)
        ·
          refine ⟨108406704482586748508261429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72271136321724499005507619 108406704482586748508261429)
          ·
            refine ⟨10163128545242507672649509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108406704482586748508261429 10163128545242507672649509)
            ·
              refine ⟨1905586602232970188621783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10163128545242507672649509 1905586602232970188621783)
              ·
                refine ⟨2858379903349455282932675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905586602232970188621783 2858379903349455282932675)
                ·
                  refine ⟨4287569855024182924399013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2858379903349455282932675 4287569855024182924399013)
                  ·
                    refine ⟨803919347817034298324815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287569855024182924399013 803919347817034298324815)
                    ·
                      rfl

theorem cell22_2348441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 4].length) (baseStart_2348441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348441 prefixEnd_2348441 := by exact prefixLift 2348441
  have htrace : WordTrace (prefixWord ++ tailWord_2348441) baseStart_2348441 baseEnd_2348441 := by
    simpa [prefixWord, tailWord_2348441, baseEnd_2348441] using wordTrace_append hprefix tailTrace_2348441
  have hstable : (prefixWord ++ tailWord_2348441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348441).length < 2 ^ (prefixWord ++ tailWord_2348441).sum := by decide
  have hdescent : baseEnd_2348441 < baseStart_2348441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348469 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2348469 : Nat := 118140960795 + 2348469 * 2 ^ 59
def prefixEnd_2348469 : Nat := 4983230072969 + 3 ^ 40 * 2348469 * 2
def baseEnd_2348469 : Nat := 803928932789251558624729

theorem tailTrace_2348469 : CollatzResearch.WordTrace tailWord_2348469 prefixEnd_2348469 803928932789251558624729 := by
  unfold tailWord_2348469
  simp only [CollatzResearch.WordTrace]
  refine ⟨85655701328905374418176461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57103800885936916278784307 85655701328905374418176461)
  ·
    refine ⟨32120887998339515406816173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85655701328905374418176461 32120887998339515406816173)
    ·
      refine ⟨12045332999377318277556065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32120887998339515406816173 12045332999377318277556065)
      ·
        refine ⟨9033999749532988708167049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12045332999377318277556065 9033999749532988708167049)
        ·
          refine ⟨6775499812149741531125287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9033999749532988708167049 6775499812149741531125287)
          ·
            refine ⟨10163249718224612296687931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775499812149741531125287 10163249718224612296687931)
            ·
              refine ⟨15244874577336918445031897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10163249718224612296687931 15244874577336918445031897)
              ·
                refine ⟨11433655933002688833773923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15244874577336918445031897 11433655933002688833773923)
                ·
                  refine ⟨17150483899504033250660885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11433655933002688833773923 17150483899504033250660885)
                  ·
                    refine ⟨803928932789251558624729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17150483899504033250660885 803928932789251558624729)
                    ·
                      rfl

theorem cell22_2348469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2348469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348469 prefixEnd_2348469 := by exact prefixLift 2348469
  have htrace : WordTrace (prefixWord ++ tailWord_2348469) baseStart_2348469 baseEnd_2348469 := by
    simpa [prefixWord, tailWord_2348469, baseEnd_2348469] using wordTrace_append hprefix tailTrace_2348469
  have hstable : (prefixWord ++ tailWord_2348469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348469).length < 2 ^ (prefixWord ++ tailWord_2348469).sum := by decide
  have hdescent : baseEnd_2348469 < baseStart_2348469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348497 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_2348497 : Nat := 118140960795 + 2348497 * 2 ^ 59
def prefixEnd_2348497 : Nat := 4983230072969 + 3 ^ 40 * 2348497 * 2
def baseEnd_2348497 : Nat := 803938517761468818924643

theorem tailTrace_2348497 : CollatzResearch.WordTrace tailWord_2348497 prefixEnd_2348497 803938517761468818924643 := by
  unfold tailWord_2348497
  simp only [CollatzResearch.WordTrace]
  refine ⟨85656722572803935200195745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57104481715202623466797163 85656722572803935200195745)
  ·
    refine ⟨64242541929602951400146809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85656722572803935200195745 64242541929602951400146809)
    ·
      refine ⟨48181906447202213550110107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64242541929602951400146809 48181906447202213550110107)
      ·
        refine ⟨72272859670803320325165161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48181906447202213550110107 72272859670803320325165161)
        ·
          refine ⟨54204644753102490243873871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72272859670803320325165161 54204644753102490243873871)
          ·
            refine ⟨81306967129653735365810807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54204644753102490243873871 81306967129653735365810807)
            ·
              refine ⟨121960450694480603048716211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81306967129653735365810807 121960450694480603048716211)
              ·
                refine ⟨182940676041720904573074317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121960450694480603048716211 182940676041720904573074317)
                ·
                  refine ⟨68602753515645339214902869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182940676041720904573074317 68602753515645339214902869)
                  ·
                    refine ⟨803938517761468818924643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68602753515645339214902869 803938517761468818924643)
                    ·
                      rfl

theorem cell22_2348497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_2348497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348497 prefixEnd_2348497 := by exact prefixLift 2348497
  have htrace : WordTrace (prefixWord ++ tailWord_2348497) baseStart_2348497 baseEnd_2348497 := by
    simpa [prefixWord, tailWord_2348497, baseEnd_2348497] using wordTrace_append hprefix tailTrace_2348497
  have hstable : (prefixWord ++ tailWord_2348497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348497).length < 2 ^ (prefixWord ++ tailWord_2348497).sum := by decide
  have hdescent : baseEnd_2348497 < baseStart_2348497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348522 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 2, 3]
def baseStart_2348522 : Nat := 118140960795 + 2348522 * 2 ^ 59
def prefixEnd_2348522 : Nat := 4983230072969 + 3 ^ 40 * 2348522 * 2
def baseEnd_2348522 : Nat := 803947075772377087049567

theorem tailTrace_2348522 : CollatzResearch.WordTrace tailWord_2348522 prefixEnd_2348522 803947075772377087049567 := by
  unfold tailWord_2348522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21414408599428341117463955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57105089598475576313237213 21414408599428341117463955)
  ·
    refine ⟨32121612899142511676195933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21414408599428341117463955 32121612899142511676195933)
    ·
      refine ⟨12045604837178441878573475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32121612899142511676195933 12045604837178441878573475)
      ·
        refine ⟨18068407255767662817860213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12045604837178441878573475 18068407255767662817860213)
        ·
          refine ⟨1693913180228218389174395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18068407255767662817860213 1693913180228218389174395)
          ·
            refine ⟨2540869770342327583761593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1693913180228218389174395 2540869770342327583761593)
            ·
              refine ⟨1905652327756745687821195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2540869770342327583761593 1905652327756745687821195)
              ·
                refine ⟨2858478491635118531731793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1905652327756745687821195 2858478491635118531731793)
                ·
                  refine ⟨2143858868726338898798845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2858478491635118531731793 2143858868726338898798845)
                  ·
                    refine ⟨803947075772377087049567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2143858868726338898798845 803947075772377087049567)
                    ·
                      rfl

theorem cell22_2348522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_2348522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348522 prefixEnd_2348522 := by exact prefixLift 2348522
  have htrace : WordTrace (prefixWord ++ tailWord_2348522) baseStart_2348522 baseEnd_2348522 := by
    simpa [prefixWord, tailWord_2348522, baseEnd_2348522] using wordTrace_append hprefix tailTrace_2348522
  have hstable : (prefixWord ++ tailWord_2348522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348522).length < 2 ^ (prefixWord ++ tailWord_2348522).sum := by decide
  have hdescent : baseEnd_2348522 < baseStart_2348522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348576 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_2348576 : Nat := 118140960795 + 2348576 * 2 ^ 59
def prefixEnd_2348576 : Nat := 4983230072969 + 3 ^ 40 * 2348576 * 2
def baseEnd_2348576 : Nat := 803965561075938946199401

theorem tailTrace_2348576 : CollatzResearch.WordTrace tailWord_2348576 prefixEnd_2348576 803965561075938946199401 := by
  unfold tailWord_2348576
  simp only [CollatzResearch.WordTrace]
  refine ⟨42829801969758865846160791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57106402626345154461547721 42829801969758865846160791)
  ·
    refine ⟨64244702954638298769241187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42829801969758865846160791 64244702954638298769241187)
    ·
      refine ⟨96367054431957448153861781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64244702954638298769241187 96367054431957448153861781)
      ·
        refine ⟨4517205676498005382212271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96367054431957448153861781 4517205676498005382212271)
        ·
          refine ⟨6775808514747008073318407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517205676498005382212271 6775808514747008073318407)
          ·
            refine ⟨10163712772120512109977611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6775808514747008073318407 10163712772120512109977611)
            ·
              refine ⟨15245569158180768164966417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10163712772120512109977611 15245569158180768164966417)
              ·
                refine ⟨11434176868635576123724813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15245569158180768164966417 11434176868635576123724813)
                ·
                  refine ⟨4287816325738341046396805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11434176868635576123724813 4287816325738341046396805)
                  ·
                    refine ⟨803965561075938946199401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4287816325738341046396805 803965561075938946199401)
                    ·
                      rfl

theorem cell22_2348576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_2348576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348576 prefixEnd_2348576 := by exact prefixLift 2348576
  have htrace : WordTrace (prefixWord ++ tailWord_2348576) baseStart_2348576 baseEnd_2348576 := by
    simpa [prefixWord, tailWord_2348576, baseEnd_2348576] using wordTrace_append hprefix tailTrace_2348576
  have hstable : (prefixWord ++ tailWord_2348576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348576).length < 2 ^ (prefixWord ++ tailWord_2348576).sum := by decide
  have hdescent : baseEnd_2348576 < baseStart_2348576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348649 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_2348649 : Nat := 118140960795 + 2348649 * 2 ^ 59
def prefixEnd_2348649 : Nat := 4983230072969 + 3 ^ 40 * 2348649 * 2
def baseEnd_2348649 : Nat := 803990550467791089124177

theorem tailTrace_2348649 : CollatzResearch.WordTrace tailWord_2348649 prefixEnd_2348649 803990550467791089124177 := by
  unfold tailWord_2348649
  simp only [CollatzResearch.WordTrace]
  refine ⟨85662266468253265159729001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57108177645502176773152667 85662266468253265159729001)
  ·
    refine ⟨64246699851189948869796751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85662266468253265159729001 64246699851189948869796751)
    ·
      refine ⟨96370049776784923304695127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64246699851189948869796751 96370049776784923304695127)
      ·
        refine ⟨144555074665177384957042691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96370049776784923304695127 144555074665177384957042691)
        ·
          refine ⟨216832611997766077435564037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144555074665177384957042691 216832611997766077435564037)
          ·
            refine ⟨40656114749581139519168257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216832611997766077435564037 40656114749581139519168257)
            ·
              refine ⟨30492086062185854639376193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40656114749581139519168257 30492086062185854639376193)
              ·
                refine ⟨22869064546639390979532145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30492086062185854639376193 22869064546639390979532145)
                ·
                  refine ⟨17151798409979543234649109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22869064546639390979532145 17151798409979543234649109)
                  ·
                    refine ⟨803990550467791089124177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17151798409979543234649109 803990550467791089124177)
                    ·
                      rfl

theorem cell22_2348649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_2348649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348649 prefixEnd_2348649 := by exact prefixLift 2348649
  have htrace : WordTrace (prefixWord ++ tailWord_2348649) baseStart_2348649 baseEnd_2348649 := by
    simpa [prefixWord, tailWord_2348649, baseEnd_2348649] using wordTrace_append hprefix tailTrace_2348649
  have hstable : (prefixWord ++ tailWord_2348649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348649).length < 2 ^ (prefixWord ++ tailWord_2348649).sum := by decide
  have hdescent : baseEnd_2348649 < baseStart_2348649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348743 : List Nat := [1, 1, 4, 1, 1, 1, 5, 4, 4]
def baseStart_2348743 : Nat := 118140960795 + 2348743 * 2 ^ 59
def prefixEnd_2348743 : Nat := 4983230072969 + 3 ^ 40 * 2348743 * 2
def baseEnd_2348743 : Nat := 268007576196268725757963

theorem tailTrace_2348743 : CollatzResearch.WordTrace tailWord_2348743 prefixEnd_2348743 268007576196268725757963 := by
  unfold tailWord_2348743
  simp only [CollatzResearch.WordTrace]
  refine ⟨85665694929912719213650883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57110463286608479475767255 85665694929912719213650883)
  ·
    refine ⟨128498542394869078820476325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85665694929912719213650883 128498542394869078820476325)
    ·
      refine ⟨24093476699037952278839311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128498542394869078820476325 24093476699037952278839311)
      ·
        refine ⟨36140215048556928418258967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24093476699037952278839311 36140215048556928418258967)
        ·
          refine ⟨54210322572835392627388451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36140215048556928418258967 54210322572835392627388451)
          ·
            refine ⟨81315483859253088941082677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54210322572835392627388451 81315483859253088941082677)
            ·
              refine ⟨7623326611804977088226501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81315483859253088941082677 7623326611804977088226501)
              ·
                refine ⟨1429373739713433204042469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7623326611804977088226501 1429373739713433204042469)
                ·
                  refine ⟨268007576196268725757963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1429373739713433204042469 268007576196268725757963)
                  ·
                    rfl

theorem cell22_2348743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 4].length) (baseStart_2348743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348743 prefixEnd_2348743 := by exact prefixLift 2348743
  have htrace : WordTrace (prefixWord ++ tailWord_2348743) baseStart_2348743 baseEnd_2348743 := by
    simpa [prefixWord, tailWord_2348743, baseEnd_2348743] using wordTrace_append hprefix tailTrace_2348743
  have hstable : (prefixWord ++ tailWord_2348743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348743).length < 2 ^ (prefixWord ++ tailWord_2348743).sum := by decide
  have hdescent : baseEnd_2348743 < baseStart_2348743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348801 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2348801 : Nat := 118140960795 + 2348801 * 2 ^ 59
def prefixEnd_2348801 : Nat := 4983230072969 + 3 ^ 40 * 2348801 * 2
def baseEnd_2348801 : Nat := 804042583174113359323711

theorem tailTrace_2348801 : CollatzResearch.WordTrace tailWord_2348801 prefixEnd_2348801 804042583174113359323711 := by
  unfold tailWord_2348801
  simp only [CollatzResearch.WordTrace]
  refine ⟨85667810363702595119262257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57111873575801730079508171 85667810363702595119262257)
  ·
    refine ⟨64250857772776946339446693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85667810363702595119262257 64250857772776946339446693)
    ·
      refine ⟨12047035832395677438646255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64250857772776946339446693 12047035832395677438646255)
      ·
        refine ⟨18070553748593516157969383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12047035832395677438646255 18070553748593516157969383)
        ·
          refine ⟨27105830622890274236954075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18070553748593516157969383 27105830622890274236954075)
          ·
            refine ⟨40658745934335411355431113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27105830622890274236954075 40658745934335411355431113)
            ·
              refine ⟨30494059450751558516573335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40658745934335411355431113 30494059450751558516573335)
              ·
                refine ⟨45741089176127337774860003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30494059450751558516573335 45741089176127337774860003)
                ·
                  refine ⟨68611633764191006662290005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45741089176127337774860003 68611633764191006662290005)
                  ·
                    refine ⟨804042583174113359323711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68611633764191006662290005 804042583174113359323711)
                    ·
                      rfl

theorem cell22_2348801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2348801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348801 prefixEnd_2348801 := by exact prefixLift 2348801
  have htrace : WordTrace (prefixWord ++ tailWord_2348801) baseStart_2348801 baseEnd_2348801 := by
    simpa [prefixWord, tailWord_2348801, baseEnd_2348801] using wordTrace_append hprefix tailTrace_2348801
  have hstable : (prefixWord ++ tailWord_2348801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348801).length < 2 ^ (prefixWord ++ tailWord_2348801).sum := by decide
  have hdescent : baseEnd_2348801 < baseStart_2348801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348803 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 3, 3]
def baseStart_2348803 : Nat := 118140960795 + 2348803 * 2 ^ 59
def prefixEnd_2348803 : Nat := 4983230072969 + 3 ^ 40 * 2348803 * 2
def baseEnd_2348803 : Nat := 804043267814986020773705

theorem tailTrace_2348803 : CollatzResearch.WordTrace tailWord_2348803 prefixEnd_2348803 804043267814986020773705 := by
  unfold tailWord_2348803
  simp only [CollatzResearch.WordTrace]
  refine ⟨85667883309695349460835063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57111922206463566307223375 85667883309695349460835063)
  ·
    refine ⟨128501824964543024191252595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85667883309695349460835063 128501824964543024191252595)
    ·
      refine ⟨192752737446814536286878893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128501824964543024191252595 192752737446814536286878893)
      ·
        refine ⟨72282276542555451107579585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192752737446814536286878893 72282276542555451107579585)
        ·
          refine ⟨54211707406916588330684689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72282276542555451107579585 54211707406916588330684689)
          ·
            refine ⟨40658780555187441248013517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54211707406916588330684689 40658780555187441248013517)
            ·
              refine ⟨15247042708195290468005069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40658780555187441248013517 15247042708195290468005069)
              ·
                refine ⟨5717641015573233925501901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15247042708195290468005069 5717641015573233925501901)
                ·
                  refine ⟨2144115380839962722063213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5717641015573233925501901 2144115380839962722063213)
                  ·
                    refine ⟨804043267814986020773705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2144115380839962722063213 804043267814986020773705)
                    ·
                      rfl

theorem cell22_2348803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 3].length) (baseStart_2348803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348803 prefixEnd_2348803 := by exact prefixLift 2348803
  have htrace : WordTrace (prefixWord ++ tailWord_2348803) baseStart_2348803 baseEnd_2348803 := by
    simpa [prefixWord, tailWord_2348803, baseEnd_2348803] using wordTrace_append hprefix tailTrace_2348803
  have hstable : (prefixWord ++ tailWord_2348803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348803).length < 2 ^ (prefixWord ++ tailWord_2348803).sum := by decide
  have hdescent : baseEnd_2348803 < baseStart_2348803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348837 : List Nat := [1, 3, 1, 2, 3, 2, 3, 3, 1, 3]
def baseStart_2348837 : Nat := 118140960795 + 2348837 * 2 ^ 59
def prefixEnd_2348837 : Nat := 4983230072969 + 3 ^ 40 * 2348837 * 2
def baseEnd_2348837 : Nat := 804054906709821265423601

theorem tailTrace_2348837 : CollatzResearch.WordTrace tailWord_2348837 prefixEnd_2348837 804054906709821265423601 := by
  unfold tailWord_2348837
  simp only [CollatzResearch.WordTrace]
  refine ⟨85669123391572173267572765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57112748927714782178381843 85669123391572173267572765)
  ·
    refine ⟨32125921271839564975339787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85669123391572173267572765 32125921271839564975339787)
    ·
      refine ⟨48188881907759347463009681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32125921271839564975339787 48188881907759347463009681)
      ·
        refine ⟨36141661430819510597257261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48188881907759347463009681 36141661430819510597257261)
        ·
          refine ⟨13553123036557316473971473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36141661430819510597257261 13553123036557316473971473)
          ·
            refine ⟨10164842277417987355478605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13553123036557316473971473 10164842277417987355478605)
            ·
              refine ⟨3811815854031745258304477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10164842277417987355478605 3811815854031745258304477)
              ·
                refine ⟨1429430945261904471864179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3811815854031745258304477 1429430945261904471864179)
                ·
                  refine ⟨2144146417892856707796269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429430945261904471864179 2144146417892856707796269)
                  ·
                    refine ⟨804054906709821265423601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2144146417892856707796269 804054906709821265423601)
                    ·
                      rfl

theorem cell22_2348837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_2348837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348837 prefixEnd_2348837 := by exact prefixLift 2348837
  have htrace : WordTrace (prefixWord ++ tailWord_2348837) baseStart_2348837 baseEnd_2348837 := by
    simpa [prefixWord, tailWord_2348837, baseEnd_2348837] using wordTrace_append hprefix tailTrace_2348837
  have hstable : (prefixWord ++ tailWord_2348837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348837).length < 2 ^ (prefixWord ++ tailWord_2348837).sum := by decide
  have hdescent : baseEnd_2348837 < baseStart_2348837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348854 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2348854 : Nat := 118140960795 + 2348854 * 2 ^ 59
def prefixEnd_2348854 : Nat := 4983230072969 + 3 ^ 40 * 2348854 * 2
def baseEnd_2348854 : Nat := 804060726157238887748549

theorem tailTrace_2348854 : CollatzResearch.WordTrace tailWord_2348854 prefixEnd_2348854 804060726157238887748549 := by
  unfold tailWord_2348854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5354358964531911573183851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57113162288340390113961077 5354358964531911573183851)
  ·
    refine ⟨8031538446797867359775777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5354358964531911573183851 8031538446797867359775777)
    ·
      refine ⟨6023653835098400519831833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8031538446797867359775777 6023653835098400519831833)
      ·
        refine ⟨4517740376323800389873875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6023653835098400519831833 4517740376323800389873875)
        ·
          refine ⟨6776610564485700584810813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517740376323800389873875 6776610564485700584810813)
          ·
            refine ⟨2541228961682137719304055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6776610564485700584810813 2541228961682137719304055)
            ·
              refine ⟨3811843442523206578956083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541228961682137719304055 3811843442523206578956083)
              ·
                refine ⟨5717765163784809868434125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3811843442523206578956083 5717765163784809868434125)
                ·
                  refine ⟨2144161936419303700662797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5717765163784809868434125 2144161936419303700662797)
                  ·
                    refine ⟨804060726157238887748549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2144161936419303700662797 804060726157238887748549)
                    ·
                      rfl

theorem cell22_2348854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2348854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348854 prefixEnd_2348854 := by exact prefixLift 2348854
  have htrace : WordTrace (prefixWord ++ tailWord_2348854) baseStart_2348854 baseEnd_2348854 := by
    simpa [prefixWord, tailWord_2348854, baseEnd_2348854] using wordTrace_append hprefix tailTrace_2348854
  have hstable : (prefixWord ++ tailWord_2348854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348854).length < 2 ^ (prefixWord ++ tailWord_2348854).sum := by decide
  have hdescent : baseEnd_2348854 < baseStart_2348854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348942 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_2348942 : Nat := 118140960795 + 2348942 * 2 ^ 59
def prefixEnd_2348942 : Nat := 4983230072969 + 3 ^ 40 * 2348942 * 2
def baseEnd_2348942 : Nat := 804090850355635991548279

theorem tailTrace_2348942 : CollatzResearch.WordTrace tailWord_2348942 prefixEnd_2348942 804090850355635991548279 := by
  unfold tailWord_2348942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10709119132023972025018135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57115302037461184133430053 10709119132023972025018135)
  ·
    refine ⟨16063678698035958037527203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10709119132023972025018135 16063678698035958037527203)
    ·
      refine ⟨24095518047053937056290805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16063678698035958037527203 24095518047053937056290805)
      ·
        refine ⟨2258954816911306599027263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24095518047053937056290805 2258954816911306599027263)
        ·
          refine ⟨3388432225366959898540895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2258954816911306599027263 3388432225366959898540895)
          ·
            refine ⟨5082648338050439847811343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3388432225366959898540895 5082648338050439847811343)
            ·
              refine ⟨7623972507075659771717015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5082648338050439847811343 7623972507075659771717015)
              ·
                refine ⟨11435958760613489657575523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7623972507075659771717015 11435958760613489657575523)
                ·
                  refine ⟨17153938140920234486363285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11435958760613489657575523 17153938140920234486363285)
                  ·
                    refine ⟨804090850355635991548279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17153938140920234486363285 804090850355635991548279)
                    ·
                      rfl

theorem cell22_2348942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_2348942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348942 prefixEnd_2348942 := by exact prefixLift 2348942
  have htrace : WordTrace (prefixWord ++ tailWord_2348942) baseStart_2348942 baseEnd_2348942 := by
    simpa [prefixWord, tailWord_2348942, baseEnd_2348942] using wordTrace_append hprefix tailTrace_2348942
  have hstable : (prefixWord ++ tailWord_2348942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348942).length < 2 ^ (prefixWord ++ tailWord_2348942).sum := by decide
  have hdescent : baseEnd_2348942 < baseStart_2348942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2348961 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 2, 3]
def baseStart_2348961 : Nat := 118140960795 + 2348961 * 2 ^ 59
def prefixEnd_2348961 : Nat := 4983230072969 + 3 ^ 40 * 2348961 * 2
def baseEnd_2348961 : Nat := 804097354443926275323221

theorem tailTrace_2348961 : CollatzResearch.WordTrace tailWord_2348961 prefixEnd_2348961 804097354443926275323221 := by
  unfold tailWord_2348961
  simp only [CollatzResearch.WordTrace]
  refine ⟨85673646043122942445086737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57115764028748628296724491 85673646043122942445086737)
  ·
    refine ⟨64255234532342206833815053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85673646043122942445086737 64255234532342206833815053)
    ·
      refine ⟨24095712949628327562680645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64255234532342206833815053 24095712949628327562680645)
      ·
        refine ⟨4517946178055311418002621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24095712949628327562680645 4517946178055311418002621)
        ·
          refine ⟨1694229816770741781750983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4517946178055311418002621 1694229816770741781750983)
          ·
            refine ⟨2541344725156112672626475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694229816770741781750983 2541344725156112672626475)
            ·
              refine ⟨3812017087734169008939713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541344725156112672626475 3812017087734169008939713)
              ·
                refine ⟨2859012815800626756704785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3812017087734169008939713 2859012815800626756704785)
                ·
                  refine ⟨2144259611850470067528589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2859012815800626756704785 2144259611850470067528589)
                  ·
                    refine ⟨804097354443926275323221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2144259611850470067528589 804097354443926275323221)
                    ·
                      rfl

theorem cell22_2348961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_2348961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2348961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2348961 prefixEnd_2348961 := by exact prefixLift 2348961
  have htrace : WordTrace (prefixWord ++ tailWord_2348961) baseStart_2348961 baseEnd_2348961 := by
    simpa [prefixWord, tailWord_2348961, baseEnd_2348961] using wordTrace_append hprefix tailTrace_2348961
  have hstable : (prefixWord ++ tailWord_2348961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2348961).length < 2 ^ (prefixWord ++ tailWord_2348961).sum := by decide
  have hdescent : baseEnd_2348961 < baseStart_2348961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2348961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349015 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 1, 4]
def baseStart_2349015 : Nat := 118140960795 + 2349015 * 2 ^ 59
def prefixEnd_2349015 : Nat := 4983230072969 + 3 ^ 40 * 2349015 * 2
def baseEnd_2349015 : Nat := 804115839747488134473055

theorem tailTrace_2349015 : CollatzResearch.WordTrace tailWord_2349015 prefixEnd_2349015 804115839747488134473055 := by
  unfold tailWord_2349015
  simp only [CollatzResearch.WordTrace]
  refine ⟨85675615584927309667552499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57117077056618206445034999 85675615584927309667552499)
  ·
    refine ⟨128513423377390964501328749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85675615584927309667552499 128513423377390964501328749)
    ·
      refine ⟨48192533766521611687998281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128513423377390964501328749 48192533766521611687998281)
      ·
        refine ⟨36144400324891208765998711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48192533766521611687998281 36144400324891208765998711)
        ·
          refine ⟨54216600487336813148998067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36144400324891208765998711 54216600487336813148998067)
          ·
            refine ⟨81324900731005219723497101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54216600487336813148998067 81324900731005219723497101)
            ·
              refine ⟨30496837774126957396311413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81324900731005219723497101 30496837774126957396311413)
              ·
                refine ⟨2859078541324402255904195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30496837774126957396311413 2859078541324402255904195)
                ·
                  refine ⟨4288617811986603383856293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859078541324402255904195 4288617811986603383856293)
                  ·
                    refine ⟨804115839747488134473055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4288617811986603383856293 804115839747488134473055)
                    ·
                      rfl

theorem cell22_2349015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_2349015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349015 prefixEnd_2349015 := by exact prefixLift 2349015
  have htrace : WordTrace (prefixWord ++ tailWord_2349015) baseStart_2349015 baseEnd_2349015 := by
    simpa [prefixWord, tailWord_2349015, baseEnd_2349015] using wordTrace_append hprefix tailTrace_2349015
  have hstable : (prefixWord ++ tailWord_2349015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349015).length < 2 ^ (prefixWord ++ tailWord_2349015).sum := by decide
  have hdescent : baseEnd_2349015 < baseStart_2349015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349043 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 3, 6]
def baseStart_2349043 : Nat := 118140960795 + 2349043 * 2 ^ 59
def prefixEnd_2349043 : Nat := 4983230072969 + 3 ^ 40 * 2349043 * 2
def baseEnd_2349043 : Nat := 804125424719705394772969

theorem tailTrace_2349043 : CollatzResearch.WordTrace tailWord_2349043 prefixEnd_2349043 804125424719705394772969 := by
  unfold tailWord_2349043
  simp only [CollatzResearch.WordTrace]
  refine ⟨85676636828825870449571783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57117757885883913633047855 85676636828825870449571783)
  ·
    refine ⟨128514955243238805674357675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85676636828825870449571783 128514955243238805674357675)
    ·
      refine ⟨192772432864858208511536513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128514955243238805674357675 192772432864858208511536513)
      ·
        refine ⟨144579324648643656383652385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192772432864858208511536513 144579324648643656383652385)
        ·
          refine ⟨108434493486482742287739289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144579324648643656383652385 108434493486482742287739289)
          ·
            refine ⟨81325870114862056715804467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108434493486482742287739289 81325870114862056715804467)
            ·
              refine ⟨121988805172293085073706701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81325870114862056715804467 121988805172293085073706701)
              ·
                refine ⟨45745801939609906902640013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121988805172293085073706701 45745801939609906902640013)
                ·
                  refine ⟨17154675727353715088490005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45745801939609906902640013 17154675727353715088490005)
                  ·
                    refine ⟨804125424719705394772969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17154675727353715088490005 804125424719705394772969)
                    ·
                      rfl

theorem cell22_2349043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_2349043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349043 prefixEnd_2349043 := by exact prefixLift 2349043
  have htrace : WordTrace (prefixWord ++ tailWord_2349043) baseStart_2349043 baseEnd_2349043 := by
    simpa [prefixWord, tailWord_2349043, baseEnd_2349043] using wordTrace_append hprefix tailTrace_2349043
  have hstable : (prefixWord ++ tailWord_2349043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349043).length < 2 ^ (prefixWord ++ tailWord_2349043).sum := by decide
  have hdescent : baseEnd_2349043 < baseStart_2349043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349167 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 1, 4]
def baseStart_2349167 : Nat := 118140960795 + 2349167 * 2 ^ 59
def prefixEnd_2349167 : Nat := 4983230072969 + 3 ^ 40 * 2349167 * 2
def baseEnd_2349167 : Nat := 804167872453810404672589

theorem tailTrace_2349167 : CollatzResearch.WordTrace tailWord_2349167 prefixEnd_2349167 804167872453810404672589 := by
  unfold tailWord_2349167
  simp only [CollatzResearch.WordTrace]
  refine ⟨85681159480376639627085755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57120772986917759751390503 85681159480376639627085755)
  ·
    refine ⟨128521739220564959440628633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85681159480376639627085755 128521739220564959440628633)
    ·
      refine ⟨96391304415423719580471475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128521739220564959440628633 96391304415423719580471475)
      ·
        refine ⟨144586956623135579370707213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96391304415423719580471475 144586956623135579370707213)
        ·
          refine ⟨54220108733675842264015205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144586956623135579370707213 54220108733675842264015205)
          ·
            refine ⟨10166270387564220424502851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54220108733675842264015205 10166270387564220424502851)
            ·
              refine ⟨15249405581346330636754277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10166270387564220424502851 15249405581346330636754277)
              ·
                refine ⟨2859263546502436994391427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15249405581346330636754277 2859263546502436994391427)
                ·
                  refine ⟨4288895319753655491587141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859263546502436994391427 4288895319753655491587141)
                  ·
                    refine ⟨804167872453810404672589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4288895319753655491587141 804167872453810404672589)
                    ·
                      rfl

theorem cell22_2349167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_2349167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349167 prefixEnd_2349167 := by exact prefixLift 2349167
  have htrace : WordTrace (prefixWord ++ tailWord_2349167) baseStart_2349167 baseEnd_2349167 := by
    simpa [prefixWord, tailWord_2349167, baseEnd_2349167] using wordTrace_append hprefix tailTrace_2349167
  have hstable : (prefixWord ++ tailWord_2349167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349167).length < 2 ^ (prefixWord ++ tailWord_2349167).sum := by decide
  have hdescent : baseEnd_2349167 < baseStart_2349167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349212 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2349212 : Nat := 118140960795 + 2349212 * 2 ^ 59
def prefixEnd_2349212 : Nat := 4983230072969 + 3 ^ 40 * 2349212 * 2
def baseEnd_2349212 : Nat := 804183276873445287297451

theorem tailTrace_2349212 : CollatzResearch.WordTrace tailWord_2349212 prefixEnd_2349212 804183276873445287297451 := by
  unfold tailWord_2349212
  simp only [CollatzResearch.WordTrace]
  refine ⟨42841400382606806156236945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57121867176809074874982593 42841400382606806156236945)
  ·
    refine ⟨32131050286955104617177709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42841400382606806156236945 32131050286955104617177709)
    ·
      refine ⟨12049143857608164231441641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32131050286955104617177709 12049143857608164231441641)
      ·
        refine ⟨9036857893206123173581231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12049143857608164231441641 9036857893206123173581231)
        ·
          refine ⟨13555286839809184760371847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9036857893206123173581231 13555286839809184760371847)
          ·
            refine ⟨20332930259713777140557771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13555286839809184760371847 20332930259713777140557771)
            ·
              refine ⟨30499395389570665710836657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20332930259713777140557771 30499395389570665710836657)
              ·
                refine ⟨22874546542177999283127493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30499395389570665710836657 22874546542177999283127493)
                ·
                  refine ⟨4288977476658374865586405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22874546542177999283127493 4288977476658374865586405)
                  ·
                    refine ⟨804183276873445287297451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4288977476658374865586405 804183276873445287297451)
                    ·
                      rfl

theorem cell22_2349212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2349212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349212 prefixEnd_2349212 := by exact prefixLift 2349212
  have htrace : WordTrace (prefixWord ++ tailWord_2349212) baseStart_2349212 baseEnd_2349212 := by
    simpa [prefixWord, tailWord_2349212, baseEnd_2349212] using wordTrace_append hprefix tailTrace_2349212
  have hstable : (prefixWord ++ tailWord_2349212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349212).length < 2 ^ (prefixWord ++ tailWord_2349212).sum := by decide
  have hdescent : baseEnd_2349212 < baseStart_2349212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349229 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2349229 : Nat := 118140960795 + 2349229 * 2 ^ 59
def prefixEnd_2349229 : Nat := 4983230072969 + 3 ^ 40 * 2349229 * 2
def baseEnd_2349229 : Nat := 804189096320862909622399

theorem tailTrace_2349229 : CollatzResearch.WordTrace tailWord_2349229 prefixEnd_2349229 804189096320862909622399 := by
  unfold tailWord_2349229
  simp only [CollatzResearch.WordTrace]
  refine ⟨85683420806152024215842741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57122280537434682810561827 85683420806152024215842741)
  ·
    refine ⟨8032820700576752270235257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85683420806152024215842741 8032820700576752270235257)
    ·
      refine ⟨6024615525432564202676443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8032820700576752270235257 6024615525432564202676443)
      ·
        refine ⟨9036923288148846304014665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024615525432564202676443 9036923288148846304014665)
        ·
          refine ⟨6777692466111634728010999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9036923288148846304014665 6777692466111634728010999)
          ·
            refine ⟨10166538699167452092016499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6777692466111634728010999 10166538699167452092016499)
            ·
              refine ⟨15249808048751178138024749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10166538699167452092016499 15249808048751178138024749)
              ·
                refine ⟨5718678018281691801759281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15249808048751178138024749 5718678018281691801759281)
                ·
                  refine ⟨4289008513711268851319461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5718678018281691801759281 4289008513711268851319461)
                  ·
                    refine ⟨804189096320862909622399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4289008513711268851319461 804189096320862909622399)
                    ·
                      rfl

theorem cell22_2349229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2349229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349229 prefixEnd_2349229 := by exact prefixLift 2349229
  have htrace : WordTrace (prefixWord ++ tailWord_2349229) baseStart_2349229 baseEnd_2349229 := by
    simpa [prefixWord, tailWord_2349229, baseEnd_2349229] using wordTrace_append hprefix tailTrace_2349229
  have hstable : (prefixWord ++ tailWord_2349229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349229).length < 2 ^ (prefixWord ++ tailWord_2349229).sum := by decide
  have hdescent : baseEnd_2349229 < baseStart_2349229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349250 : List Nat := [3, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2349250 : Nat := 118140960795 + 2349250 * 2 ^ 59
def prefixEnd_2349250 : Nat := 4983230072969 + 3 ^ 40 * 2349250 * 2
def baseEnd_2349250 : Nat := 268065428350008618282445

theorem tailTrace_2349250 : CollatzResearch.WordTrace tailWord_2349250 prefixEnd_2349250 268065428350008618282445 := by
  unfold tailWord_2349250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21421046684768986200589301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57122791159383963201571469 21421046684768986200589301)
  ·
    refine ⟨2008223126697092456305247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21421046684768986200589301 2008223126697092456305247)
    ·
      refine ⟨3012334690045638684457871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008223126697092456305247 3012334690045638684457871)
      ·
        refine ⟨4518502035068458026686807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012334690045638684457871 4518502035068458026686807)
        ·
          refine ⟨6777753052602687040030211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4518502035068458026686807 6777753052602687040030211)
          ·
            refine ⟨10166629578904030560045317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6777753052602687040030211 10166629578904030560045317)
            ·
              refine ⟨1906243046044505730008497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10166629578904030560045317 1906243046044505730008497)
              ·
                refine ⟨1429682284533379297506373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906243046044505730008497 1429682284533379297506373)
                ·
                  refine ⟨268065428350008618282445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1429682284533379297506373 268065428350008618282445)
                  ·
                    rfl

theorem cell22_2349250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2349250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349250 prefixEnd_2349250 := by exact prefixLift 2349250
  have htrace : WordTrace (prefixWord ++ tailWord_2349250) baseStart_2349250 baseEnd_2349250 := by
    simpa [prefixWord, tailWord_2349250, baseEnd_2349250] using wordTrace_append hprefix tailTrace_2349250
  have hstable : (prefixWord ++ tailWord_2349250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349250).length < 2 ^ (prefixWord ++ tailWord_2349250).sum := by decide
  have hdescent : baseEnd_2349250 < baseStart_2349250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349347 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 1, 6]
def baseStart_2349347 : Nat := 118140960795 + 2349347 * 2 ^ 59
def prefixEnd_2349347 : Nat := 4983230072969 + 3 ^ 40 * 2349347 * 2
def baseEnd_2349347 : Nat := 804229490132349935172037

theorem tailTrace_2349347 : CollatzResearch.WordTrace tailWord_2349347 prefixEnd_2349347 804229490132349935172037 := by
  unfold tailWord_2349347
  simp only [CollatzResearch.WordTrace]
  refine ⟨85687724619724530368638295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57125149746483020245758863 85687724619724530368638295)
  ·
    refine ⟨128531586929586795552957443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85687724619724530368638295 128531586929586795552957443)
    ·
      refine ⟨192797380394380193329436165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128531586929586795552957443 192797380394380193329436165)
      ·
        refine ⟨36149508823946286249269281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192797380394380193329436165 36149508823946286249269281)
        ·
          refine ⟨27112131617959714686951961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36149508823946286249269281 27112131617959714686951961)
          ·
            refine ⟨20334098713469786015213971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27112131617959714686951961 20334098713469786015213971)
            ·
              refine ⟨30501148070204679022820957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20334098713469786015213971 30501148070204679022820957)
              ·
                refine ⟨11437930526326754633557859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30501148070204679022820957 11437930526326754633557859)
                ·
                  refine ⟨17156895789490131950336789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11437930526326754633557859 17156895789490131950336789)
                  ·
                    refine ⟨804229490132349935172037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17156895789490131950336789 804229490132349935172037)
                    ·
                      rfl

theorem cell22_2349347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_2349347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349347 prefixEnd_2349347 := by exact prefixLift 2349347
  have htrace : WordTrace (prefixWord ++ tailWord_2349347) baseStart_2349347 baseEnd_2349347 := by
    simpa [prefixWord, tailWord_2349347, baseEnd_2349347] using wordTrace_append hprefix tailTrace_2349347
  have hstable : (prefixWord ++ tailWord_2349347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349347).length < 2 ^ (prefixWord ++ tailWord_2349347).sum := by decide
  have hdescent : baseEnd_2349347 < baseStart_2349347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349407 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 9]
def baseStart_2349407 : Nat := 118140960795 + 2349407 * 2 ^ 59
def prefixEnd_2349407 : Nat := 4983230072969 + 3 ^ 40 * 2349407 * 2
def baseEnd_2349407 : Nat := 268083343119509926223951

theorem tailTrace_2349407 : CollatzResearch.WordTrace tailWord_2349407 prefixEnd_2349407 268083343119509926223951 := by
  unfold tailWord_2349407
  simp only [CollatzResearch.WordTrace]
  refine ⟨85689912999507160615822475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57126608666338107077214983 85689912999507160615822475)
  ·
    refine ⟨128534869499260740923733713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85689912999507160615822475 128534869499260740923733713)
    ·
      refine ⟨96401152124445555692800285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128534869499260740923733713 96401152124445555692800285)
      ·
        refine ⟨36150432046667083384800107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96401152124445555692800285 36150432046667083384800107)
        ·
          refine ⟨54225648070000625077200161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36150432046667083384800107 54225648070000625077200161)
          ·
            refine ⟨40669236052500468807900121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54225648070000625077200161 40669236052500468807900121)
            ·
              refine ⟨30501927039375351605925091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40669236052500468807900121 30501927039375351605925091)
              ·
                refine ⟨45752890559063027408887637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30501927039375351605925091 45752890559063027408887637)
                ·
                  refine ⟨268083343119509926223951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45752890559063027408887637 268083343119509926223951)
                  ·
                    rfl

theorem cell22_2349407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 9].length) (baseStart_2349407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349407 prefixEnd_2349407 := by exact prefixLift 2349407
  have htrace : WordTrace (prefixWord ++ tailWord_2349407) baseStart_2349407 baseEnd_2349407 := by
    simpa [prefixWord, tailWord_2349407, baseEnd_2349407] using wordTrace_append hprefix tailTrace_2349407
  have hstable : (prefixWord ++ tailWord_2349407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349407).length < 2 ^ (prefixWord ++ tailWord_2349407).sum := by decide
  have hdescent : baseEnd_2349407 < baseStart_2349407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349424 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 5]
def baseStart_2349424 : Nat := 118140960795 + 2349424 * 2 ^ 59
def prefixEnd_2349424 : Nat := 4983230072969 + 3 ^ 40 * 2349424 * 2
def baseEnd_2349424 : Nat := 268085282935315800332267

theorem tailTrace_2349424 : CollatzResearch.WordTrace tailWord_2349424 prefixEnd_2349424 268085282935315800332267 := by
  unfold tailWord_2349424
  simp only [CollatzResearch.WordTrace]
  refine ⟨42845266520222786259595663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57127022026963715012794217 42845266520222786259595663)
  ·
    refine ⟨64267899780334179389393495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42845266520222786259595663 64267899780334179389393495)
    ·
      refine ⟨96401849670501269084090243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64267899780334179389393495 96401849670501269084090243)
      ·
        refine ⟨144602774505751903626135365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96401849670501269084090243 144602774505751903626135365)
        ·
          refine ⟨27113020219828481929900381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144602774505751903626135365 27113020219828481929900381)
          ·
            refine ⟨10167382582435680723712643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27113020219828481929900381 10167382582435680723712643)
            ·
              refine ⟨15251073873653521085568965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10167382582435680723712643 15251073873653521085568965)
              ·
                refine ⟨2859576351310035203544181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15251073873653521085568965 2859576351310035203544181)
                ·
                  refine ⟨268085282935315800332267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2859576351310035203544181 268085282935315800332267)
                  ·
                    rfl

theorem cell22_2349424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_2349424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349424 prefixEnd_2349424 := by exact prefixLift 2349424
  have htrace : WordTrace (prefixWord ++ tailWord_2349424) baseStart_2349424 baseEnd_2349424 := by
    simpa [prefixWord, tailWord_2349424, baseEnd_2349424] using wordTrace_append hprefix tailTrace_2349424
  have hstable : (prefixWord ++ tailWord_2349424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349424).length < 2 ^ (prefixWord ++ tailWord_2349424).sum := by decide
  have hdescent : baseEnd_2349424 < baseStart_2349424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349430 : List Nat := [5, 1, 1, 4, 2, 1, 1, 7]
def baseStart_2349430 : Nat := 118140960795 + 2349430 * 2 ^ 59
def prefixEnd_2349430 : Nat := 4983230072969 + 3 ^ 40 * 2349430 * 2
def baseEnd_2349430 : Nat := 89361989192062820594087

theorem tailTrace_2349430 : CollatzResearch.WordTrace tailWord_2349430 prefixEnd_2349430 89361989192062820594087 := by
  unfold tailWord_2349430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5355671992401489721494359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57127167918949223695939829 5355671992401489721494359)
  ·
    refine ⟨8033507988602234582241539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5355671992401489721494359 8033507988602234582241539)
    ·
      refine ⟨12050261982903351873362309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8033507988602234582241539 12050261982903351873362309)
      ·
        refine ⟨2259424121794378476255433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12050261982903351873362309 2259424121794378476255433)
        ·
          refine ⟨1694568091345783857191575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2259424121794378476255433 1694568091345783857191575)
          ·
            refine ⟨2541852137018675785787363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694568091345783857191575 2541852137018675785787363)
            ·
              refine ⟨3812778205528013678681045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541852137018675785787363 3812778205528013678681045)
              ·
                refine ⟨89361989192062820594087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3812778205528013678681045 89361989192062820594087)
                ·
                  rfl

theorem cell22_2349430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_2349430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349430 prefixEnd_2349430 := by exact prefixLift 2349430
  have htrace : WordTrace (prefixWord ++ tailWord_2349430) baseStart_2349430 baseEnd_2349430 := by
    simpa [prefixWord, tailWord_2349430, baseEnd_2349430] using wordTrace_append hprefix tailTrace_2349430
  have hstable : (prefixWord ++ tailWord_2349430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349430).length < 2 ^ (prefixWord ++ tailWord_2349430).sum := by decide
  have hdescent : baseEnd_2349430 < baseStart_2349430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349441 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 5]
def baseStart_2349441 : Nat := 118140960795 + 2349441 * 2 ^ 59
def prefixEnd_2349441 : Nat := 4983230072969 + 3 ^ 40 * 2349441 * 2
def baseEnd_2349441 : Nat := 268087222751121674440583

theorem tailTrace_2349441 : CollatzResearch.WordTrace tailWord_2349441 prefixEnd_2349441 268087222751121674440583 := by
  unfold tailWord_2349441
  simp only [CollatzResearch.WordTrace]
  refine ⟨85691153081383984422560177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57127435387589322948373451 85691153081383984422560177)
  ·
    refine ⟨64268364811037988316920133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85691153081383984422560177 64268364811037988316920133)
    ·
      refine ⟨12050318402069622809422525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64268364811037988316920133 12050318402069622809422525)
      ·
        refine ⟨4518869400776108553533447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12050318402069622809422525 4518869400776108553533447)
        ·
          refine ⟨6778304101164162830300171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4518869400776108553533447 6778304101164162830300171)
          ·
            refine ⟨10167456151746244245450257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6778304101164162830300171 10167456151746244245450257)
            ·
              refine ⟨7625592113809683184087693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10167456151746244245450257 7625592113809683184087693)
              ·
                refine ⟨2859597042678631194032885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7625592113809683184087693 2859597042678631194032885)
                ·
                  refine ⟨268087222751121674440583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2859597042678631194032885 268087222751121674440583)
                  ·
                    rfl

theorem cell22_2349441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_2349441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349441 prefixEnd_2349441 := by exact prefixLift 2349441
  have htrace : WordTrace (prefixWord ++ tailWord_2349441) baseStart_2349441 baseEnd_2349441 := by
    simpa [prefixWord, tailWord_2349441, baseEnd_2349441] using wordTrace_append hprefix tailTrace_2349441
  have hstable : (prefixWord ++ tailWord_2349441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349441).length < 2 ^ (prefixWord ++ tailWord_2349441).sum := by decide
  have hdescent : baseEnd_2349441 < baseStart_2349441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349471 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 1, 4]
def baseStart_2349471 : Nat := 118140960795 + 2349471 * 2 ^ 59
def prefixEnd_2349471 : Nat := 4983230072969 + 3 ^ 40 * 2349471 * 2
def baseEnd_2349471 : Nat := 804271937866454945071657

theorem tailTrace_2349471 : CollatzResearch.WordTrace tailWord_2349471 prefixEnd_2349471 804271937866454945071657 := by
  unfold tailWord_2349471
  simp only [CollatzResearch.WordTrace]
  refine ⟨85692247271275299546152267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57128164847516866364101511 85692247271275299546152267)
  ·
    refine ⟨128538370906912949319228401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85692247271275299546152267 128538370906912949319228401)
    ·
      refine ⟨96403778180184711989421301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128538370906912949319228401 96403778180184711989421301)
      ·
        refine ⟨9037854204392316749008247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96403778180184711989421301 9037854204392316749008247)
        ·
          refine ⟨13556781306588475123512371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9037854204392316749008247 13556781306588475123512371)
          ·
            refine ⟨20335171959882712685268557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13556781306588475123512371 20335171959882712685268557)
            ·
              refine ⟨7625689484956017256975709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20335171959882712685268557 7625689484956017256975709)
              ·
                refine ⟨2859633556858506471365891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7625689484956017256975709 2859633556858506471365891)
                ·
                  refine ⟨4289450335287759707048837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2859633556858506471365891 4289450335287759707048837)
                  ·
                    refine ⟨804271937866454945071657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4289450335287759707048837 804271937866454945071657)
                    ·
                      rfl

theorem cell22_2349471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_2349471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349471 prefixEnd_2349471 := by exact prefixLift 2349471
  have htrace : WordTrace (prefixWord ++ tailWord_2349471) baseStart_2349471 baseEnd_2349471 := by
    simpa [prefixWord, tailWord_2349471, baseEnd_2349471] using wordTrace_append hprefix tailTrace_2349471
  have hstable : (prefixWord ++ tailWord_2349471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349471).length < 2 ^ (prefixWord ++ tailWord_2349471).sum := by decide
  have hdescent : baseEnd_2349471 < baseStart_2349471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349492 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2349492 : Nat := 118140960795 + 2349492 * 2 ^ 59
def prefixEnd_2349492 : Nat := 4983230072969 + 3 ^ 40 * 2349492 * 2
def baseEnd_2349492 : Nat := 268093042198539296765531

theorem tailTrace_2349492 : CollatzResearch.WordTrace tailWord_2349492 prefixEnd_2349492 268093042198539296765531 := by
  unfold tailWord_2349492
  simp only [CollatzResearch.WordTrace]
  refine ⟨42846506602099610066333365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57128675469466146755111153 42846506602099610066333365)
  ·
    refine ⟨4016859993946838443718753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42846506602099610066333365 4016859993946838443718753)
    ·
      refine ⟨3012644995460128832789065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4016859993946838443718753 3012644995460128832789065)
      ·
        refine ⟨2259483746595096624591799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3012644995460128832789065 2259483746595096624591799)
        ·
          refine ⟨3389225619892644936887699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2259483746595096624591799 3389225619892644936887699)
          ·
            refine ⟨5083838429838967405331549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3389225619892644936887699 5083838429838967405331549)
            ·
              refine ⟨1906439411189612776999331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5083838429838967405331549 1906439411189612776999331)
              ·
                refine ⟨2859659116784419165498997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906439411189612776999331 2859659116784419165498997)
                ·
                  refine ⟨268093042198539296765531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2859659116784419165498997 268093042198539296765531)
                  ·
                    rfl

theorem cell22_2349492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2349492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349492 prefixEnd_2349492 := by exact prefixLift 2349492
  have htrace : WordTrace (prefixWord ++ tailWord_2349492) baseStart_2349492 baseEnd_2349492 := by
    simpa [prefixWord, tailWord_2349492, baseEnd_2349492] using wordTrace_append hprefix tailTrace_2349492
  have hstable : (prefixWord ++ tailWord_2349492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349492).length < 2 ^ (prefixWord ++ tailWord_2349492).sum := by decide
  have hdescent : baseEnd_2349492 < baseStart_2349492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349501 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_2349501 : Nat := 118140960795 + 2349501 * 2 ^ 59
def prefixEnd_2349501 : Nat := 4983230072969 + 3 ^ 40 * 2349501 * 2
def baseEnd_2349501 : Nat := 804282207479544866821565

theorem tailTrace_2349501 : CollatzResearch.WordTrace tailWord_2349501 prefixEnd_2349501 804282207479544866821565 := by
  unfold tailWord_2349501
  simp only [CollatzResearch.WordTrace]
  refine ⟨85693341461166614669744357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57128894307444409779829571 85693341461166614669744357)
  ·
    refine ⟨16067501523968740250577067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85693341461166614669744357 16067501523968740250577067)
    ·
      refine ⟨24101252285953110375865601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16067501523968740250577067 24101252285953110375865601)
      ·
        refine ⟨18075939214464832781899201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24101252285953110375865601 18075939214464832781899201)
        ·
          refine ⟨13556954410848624586424401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18075939214464832781899201 13556954410848624586424401)
          ·
            refine ⟨10167715808136468439818301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13556954410848624586424401 10167715808136468439818301)
            ·
              refine ⟨3812893428051175664931863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10167715808136468439818301 3812893428051175664931863)
              ·
                refine ⟨5719340142076763497397795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812893428051175664931863 5719340142076763497397795)
                ·
                  refine ⟨8579010213115145246096693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5719340142076763497397795 8579010213115145246096693)
                  ·
                    refine ⟨804282207479544866821565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8579010213115145246096693 804282207479544866821565)
                    ·
                      rfl

theorem cell22_2349501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_2349501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349501 prefixEnd_2349501 := by exact prefixLift 2349501
  have htrace : WordTrace (prefixWord ++ tailWord_2349501) baseStart_2349501 baseEnd_2349501 := by
    simpa [prefixWord, tailWord_2349501, baseEnd_2349501] using wordTrace_append hprefix tailTrace_2349501
  have hstable : (prefixWord ++ tailWord_2349501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349501).length < 2 ^ (prefixWord ++ tailWord_2349501).sum := by decide
  have hdescent : baseEnd_2349501 < baseStart_2349501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349514 : List Nat := [3, 1, 2, 1, 2, 2, 3, 8]
def baseStart_2349514 : Nat := 118140960795 + 2349514 * 2 ^ 59
def prefixEnd_2349514 : Nat := 4983230072969 + 3 ^ 40 * 2349514 * 2
def baseEnd_2349514 : Nat := 89365184182801907360725

theorem tailTrace_2349514 : CollatzResearch.WordTrace tailWord_2349514 prefixEnd_2349514 89365184182801907360725 := by
  unfold tailWord_2349514
  simp only [CollatzResearch.WordTrace]
  refine ⟨21423453902529879472491899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57129210406746345259978397 21423453902529879472491899)
  ·
    refine ⟨32135180853794819208737849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21423453902529879472491899 32135180853794819208737849)
    ·
      refine ⟨24101385640346114406553387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32135180853794819208737849 24101385640346114406553387)
      ·
        refine ⟨36152078460519171609830081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24101385640346114406553387 36152078460519171609830081)
        ·
          refine ⟨27114058845389378707372561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36152078460519171609830081 27114058845389378707372561)
          ·
            refine ⟨20335544134042034030529421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27114058845389378707372561 20335544134042034030529421)
            ·
              refine ⟨7625829050265762761448533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20335544134042034030529421 7625829050265762761448533)
              ·
                refine ⟨89365184182801907360725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7625829050265762761448533 89365184182801907360725)
                ·
                  rfl

theorem cell22_2349514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_2349514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349514 prefixEnd_2349514 := by exact prefixLift 2349514
  have htrace : WordTrace (prefixWord ++ tailWord_2349514) baseStart_2349514 baseEnd_2349514 := by
    simpa [prefixWord, tailWord_2349514, baseEnd_2349514] using wordTrace_append hprefix tailTrace_2349514
  have hstable : (prefixWord ++ tailWord_2349514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349514).length < 2 ^ (prefixWord ++ tailWord_2349514).sum := by decide
  have hdescent : baseEnd_2349514 < baseStart_2349514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349597 : List Nat := [1, 4, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_2349597 : Nat := 118140960795 + 2349597 * 2 ^ 59
def prefixEnd_2349597 : Nat := 4983230072969 + 3 ^ 40 * 2349597 * 2
def baseEnd_2349597 : Nat := 804315070241432616421271

theorem tailTrace_2349597 : CollatzResearch.WordTrace tailWord_2349597 prefixEnd_2349597 804315070241432616421271 := by
  unfold tailWord_2349597
  simp only [CollatzResearch.WordTrace]
  refine ⟨85696842868818823065239045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57131228579212548710159363 85696842868818823065239045)
  ·
    refine ⟨16068158037903529324732321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85696842868818823065239045 16068158037903529324732321)
    ·
      refine ⟨12051118528427646993549241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16068158037903529324732321 12051118528427646993549241)
      ·
        refine ⟨9038338896320735245161931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12051118528427646993549241 9038338896320735245161931)
        ·
          refine ⟨13557508344481102867742897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9038338896320735245161931 13557508344481102867742897)
          ·
            refine ⟨10168131258360827150807173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13557508344481102867742897 10168131258360827150807173)
            ·
              refine ⟨1906524610942655090776345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10168131258360827150807173 1906524610942655090776345)
              ·
                refine ⟨1429893458206991318082259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906524610942655090776345 1429893458206991318082259)
                ·
                  refine ⟨2144840187310486977123389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1429893458206991318082259 2144840187310486977123389)
                  ·
                    refine ⟨804315070241432616421271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2144840187310486977123389 804315070241432616421271)
                    ·
                      rfl

theorem cell22_2349597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_2349597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349597 prefixEnd_2349597 := by exact prefixLift 2349597
  have htrace : WordTrace (prefixWord ++ tailWord_2349597) baseStart_2349597 baseEnd_2349597 := by
    simpa [prefixWord, tailWord_2349597, baseEnd_2349597] using wordTrace_append hprefix tailTrace_2349597
  have hstable : (prefixWord ++ tailWord_2349597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349597).length < 2 ^ (prefixWord ++ tailWord_2349597).sum := by decide
  have hdescent : baseEnd_2349597 < baseStart_2349597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349608 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_2349608 : Nat := 118140960795 + 2349608 * 2 ^ 59
def prefixEnd_2349608 : Nat := 4983230072969 + 3 ^ 40 * 2349608 * 2
def baseEnd_2349608 : Nat := 804318835766232254396237

theorem tailTrace_2349608 : CollatzResearch.WordTrace tailWord_2349608 prefixEnd_2349608 804318835766232254396237 := by
  unfold tailWord_2349608
  simp only [CollatzResearch.WordTrace]
  refine ⟨42848622035889485971944739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57131496047852647962592985 42848622035889485971944739)
  ·
    refine ⟨64272933053834228957917109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42848622035889485971944739 64272933053834228957917109)
    ·
      refine ⟨6025587473796958964804729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64272933053834228957917109 6025587473796958964804729)
      ·
        refine ⟨4519190605347719223603547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6025587473796958964804729 4519190605347719223603547)
        ·
          refine ⟨6778785908021578835405321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519190605347719223603547 6778785908021578835405321)
          ·
            refine ⟨5084089431016184126553991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6778785908021578835405321 5084089431016184126553991)
            ·
              refine ⟨7626134146524276189830987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084089431016184126553991 7626134146524276189830987)
              ·
                refine ⟨11439201219786414284746481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626134146524276189830987 11439201219786414284746481)
                ·
                  refine ⟨8579400914839810713559861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11439201219786414284746481 8579400914839810713559861)
                  ·
                    refine ⟨804318835766232254396237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8579400914839810713559861 804318835766232254396237)
                    ·
                      rfl

theorem cell22_2349608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_2349608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349608 prefixEnd_2349608 := by exact prefixLift 2349608
  have htrace : WordTrace (prefixWord ++ tailWord_2349608) baseStart_2349608 baseEnd_2349608 := by
    simpa [prefixWord, tailWord_2349608, baseEnd_2349608] using wordTrace_append hprefix tailTrace_2349608
  have hstable : (prefixWord ++ tailWord_2349608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349608).length < 2 ^ (prefixWord ++ tailWord_2349608).sum := by decide
  have hdescent : baseEnd_2349608 < baseStart_2349608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349621 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 6]
def baseStart_2349621 : Nat := 118140960795 + 2349621 * 2 ^ 59
def prefixEnd_2349621 : Nat := 4983230072969 + 3 ^ 40 * 2349621 * 2
def baseEnd_2349621 : Nat := 268107761977301517940399

theorem tailTrace_2349621 : CollatzResearch.WordTrace tailWord_2349621 prefixEnd_2349621 268107761977301517940399 := by
  unfold tailWord_2349621
  simp only [CollatzResearch.WordTrace]
  refine ⟨85697718220731875164112717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57131812147154583442741811 85697718220731875164112717)
  ·
    refine ⟨32136644332774453186542269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85697718220731875164112717 32136644332774453186542269)
    ·
      refine ⟨12051241624790419944953351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32136644332774453186542269 12051241624790419944953351)
      ·
        refine ⟨18076862437185629917430027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12051241624790419944953351 18076862437185629917430027)
        ·
          refine ⟨27115293655778444876145041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18076862437185629917430027 27115293655778444876145041)
          ·
            refine ⟨20336470241833833657108781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27115293655778444876145041 20336470241833833657108781)
            ·
              refine ⟨7626176340687687621415793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20336470241833833657108781 7626176340687687621415793)
              ·
                refine ⟨5719632255515765716061845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7626176340687687621415793 5719632255515765716061845)
                ·
                  refine ⟨268107761977301517940399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5719632255515765716061845 268107761977301517940399)
                  ·
                    rfl

theorem cell22_2349621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_2349621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349621 prefixEnd_2349621 := by exact prefixLift 2349621
  have htrace : WordTrace (prefixWord ++ tailWord_2349621) baseStart_2349621 baseEnd_2349621 := by
    simpa [prefixWord, tailWord_2349621, baseEnd_2349621] using wordTrace_append hprefix tailTrace_2349621
  have hstable : (prefixWord ++ tailWord_2349621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349621).length < 2 ^ (prefixWord ++ tailWord_2349621).sum := by decide
  have hdescent : baseEnd_2349621 < baseStart_2349621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349801 : List Nat := [1, 2, 1, 1, 1, 2, 4, 10]
def baseStart_2349801 : Nat := 118140960795 + 2349801 * 2 ^ 59
def prefixEnd_2349801 : Nat := 4983230072969 + 3 ^ 40 * 2349801 * 2
def baseEnd_2349801 : Nat := 89376100401160453813405

theorem tailTrace_2349801 : CollatzResearch.WordTrace tailWord_2349801 prefixEnd_2349801 89376100401160453813405 := by
  unfold tailWord_2349801
  simp only [CollatzResearch.WordTrace]
  refine ⟨85704283360079765905665257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57136188906719843937110171 85704283360079765905665257)
  ·
    refine ⟨64278212520059824429248943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85704283360079765905665257 64278212520059824429248943)
    ·
      refine ⟨96417318780089736643873415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64278212520059824429248943 96417318780089736643873415)
      ·
        refine ⟨144625978170134604965810123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96417318780089736643873415 144625978170134604965810123)
        ·
          refine ⟨216938967255201907448715185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144625978170134604965810123 216938967255201907448715185)
          ·
            refine ⟨162704225441401430586536389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216938967255201907448715185 162704225441401430586536389)
            ·
              refine ⟨30507042270262768234975573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162704225441401430586536389 30507042270262768234975573)
              ·
                refine ⟨89376100401160453813405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30507042270262768234975573 89376100401160453813405)
                ·
                  rfl

theorem cell22_2349801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 10].length) (baseStart_2349801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349801 prefixEnd_2349801 := by exact prefixLift 2349801
  have htrace : WordTrace (prefixWord ++ tailWord_2349801) baseStart_2349801 baseEnd_2349801 := by
    simpa [prefixWord, tailWord_2349801, baseEnd_2349801] using wordTrace_append hprefix tailTrace_2349801
  have hstable : (prefixWord ++ tailWord_2349801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349801).length < 2 ^ (prefixWord ++ tailWord_2349801).sum := by decide
  have hdescent : baseEnd_2349801 < baseStart_2349801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349805 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_2349805 : Nat := 118140960795 + 2349805 * 2 ^ 59
def prefixEnd_2349805 : Nat := 4983230072969 + 3 ^ 40 * 2349805 * 2
def baseEnd_2349805 : Nat := 804386272892189407220633

theorem tailTrace_2349805 : CollatzResearch.WordTrace tailWord_2349805 prefixEnd_2349805 804386272892189407220633 := by
  unfold tailWord_2349805
  simp only [CollatzResearch.WordTrace]
  refine ⟨85704429252065274588810869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57136286168043516392540579 85704429252065274588810869)
  ·
    refine ⟨8034790242381119492701019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85704429252065274588810869 8034790242381119492701019)
    ·
      refine ⟨12052185363571679239051529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8034790242381119492701019 12052185363571679239051529)
      ·
        refine ⟨9039139022678759429288647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12052185363571679239051529 9039139022678759429288647)
        ·
          refine ⟨13558708534018139143932971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9039139022678759429288647 13558708534018139143932971)
          ·
            refine ⟨20338062801027208715899457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13558708534018139143932971 20338062801027208715899457)
            ·
              refine ⟨15253547100770406536924593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20338062801027208715899457 15253547100770406536924593)
              ·
                refine ⟨11440160325577804902693445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15253547100770406536924593 11440160325577804902693445)
                ·
                  refine ⟨2145030061045838419255021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11440160325577804902693445 2145030061045838419255021)
                  ·
                    refine ⟨804386272892189407220633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145030061045838419255021 804386272892189407220633)
                    ·
                      rfl

theorem cell22_2349805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_2349805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349805 prefixEnd_2349805 := by exact prefixLift 2349805
  have htrace : WordTrace (prefixWord ++ tailWord_2349805) baseStart_2349805 baseEnd_2349805 := by
    simpa [prefixWord, tailWord_2349805, baseEnd_2349805] using wordTrace_append hprefix tailTrace_2349805
  have hstable : (prefixWord ++ tailWord_2349805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349805).length < 2 ^ (prefixWord ++ tailWord_2349805).sum := by decide
  have hdescent : baseEnd_2349805 < baseStart_2349805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349822 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_2349822 : Nat := 118140960795 + 2349822 * 2 ^ 59
def prefixEnd_2349822 : Nat := 4983230072969 + 3 ^ 40 * 2349822 * 2
def baseEnd_2349822 : Nat := 804392092339607029545581

theorem tailTrace_2349822 : CollatzResearch.WordTrace tailWord_2349822 prefixEnd_2349822 804392092339607029545581 := by
  unfold tailWord_2349822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10713131161625460811522465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57136699528669124328119813 10713131161625460811522465)
  ·
    refine ⟨8034848371219095608641849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10713131161625460811522465 8034848371219095608641849)
    ·
      refine ⟨6026136278414321706481387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8034848371219095608641849 6026136278414321706481387)
      ·
        refine ⟨9039204417621482559722081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026136278414321706481387 9039204417621482559722081)
        ·
          refine ⟨6779403313216111919791561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9039204417621482559722081 6779403313216111919791561)
          ·
            refine ⟨5084552484912083939843671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6779403313216111919791561 5084552484912083939843671)
            ·
              refine ⟨7626828727368125909765507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5084552484912083939843671 7626828727368125909765507)
              ·
                refine ⟨11440243091052188864648261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7626828727368125909765507 11440243091052188864648261)
                ·
                  refine ⟨2145045579572285412121549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11440243091052188864648261 2145045579572285412121549)
                  ·
                    refine ⟨804392092339607029545581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145045579572285412121549 804392092339607029545581)
                    ·
                      rfl

theorem cell22_2349822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_2349822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349822 prefixEnd_2349822 := by exact prefixLift 2349822
  have htrace : WordTrace (prefixWord ++ tailWord_2349822) baseStart_2349822 baseEnd_2349822 := by
    simpa [prefixWord, tailWord_2349822, baseEnd_2349822] using wordTrace_append hprefix tailTrace_2349822
  have hstable : (prefixWord ++ tailWord_2349822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349822).length < 2 ^ (prefixWord ++ tailWord_2349822).sum := by decide
  have hdescent : baseEnd_2349822 < baseStart_2349822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349850 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_2349850 : Nat := 118140960795 + 2349850 * 2 ^ 59
def prefixEnd_2349850 : Nat := 4983230072969 + 3 ^ 40 * 2349850 * 2
def baseEnd_2349850 : Nat := 804401677311824289845495

theorem tailTrace_2349850 : CollatzResearch.WordTrace tailWord_2349850 prefixEnd_2349850 804401677311824289845495 := by
  unfold tailWord_2349850
  simp only [CollatzResearch.WordTrace]
  refine ⟨21426517634225561818549751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57137380357934831516132669 21426517634225561818549751)
  ·
    refine ⟨32139776451338342727824627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21426517634225561818549751 32139776451338342727824627)
    ·
      refine ⟨48209664677007514091736941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32139776451338342727824627 48209664677007514091736941)
      ·
        refine ⟨18078624253877817784401353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48209664677007514091736941 18078624253877817784401353)
        ·
          refine ⟨13558968190408363338301015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18078624253877817784401353 13558968190408363338301015)
          ·
            refine ⟨20338452285612545007451523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13558968190408363338301015 20338452285612545007451523)
            ·
              refine ⟨30507678428418817511177285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20338452285612545007451523 30507678428418817511177285)
              ·
                refine ⟨5720189705328528283345741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30507678428418817511177285 5720189705328528283345741)
                ·
                  refine ⟨2145071139498198106254653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5720189705328528283345741 2145071139498198106254653)
                  ·
                    refine ⟨804401677311824289845495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145071139498198106254653 804401677311824289845495)
                    ·
                      rfl

theorem cell22_2349850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_2349850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349850 prefixEnd_2349850 := by exact prefixLift 2349850
  have htrace : WordTrace (prefixWord ++ tailWord_2349850) baseStart_2349850 baseEnd_2349850 := by
    simpa [prefixWord, tailWord_2349850, baseEnd_2349850] using wordTrace_append hprefix tailTrace_2349850
  have hstable : (prefixWord ++ tailWord_2349850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349850).length < 2 ^ (prefixWord ++ tailWord_2349850).sum := by decide
  have hdescent : baseEnd_2349850 < baseStart_2349850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349869 : List Nat := [1, 5, 3, 2, 2, 1, 8]
def baseStart_2349869 : Nat := 118140960795 + 2349869 * 2 ^ 59
def prefixEnd_2349869 : Nat := 4983230072969 + 3 ^ 40 * 2349869 * 2
def baseEnd_2349869 : Nat := 29792895607411650874831

theorem tailTrace_2349869 : CollatzResearch.WordTrace tailWord_2349869 prefixEnd_2349869 29792895607411650874831 := by
  unfold tailWord_2349869
  simp only [CollatzResearch.WordTrace]
  refine ⟨85706763523833413519140661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57137842349222275679427107 85706763523833413519140661)
  ·
    refine ⟨8035009080359382517419437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85706763523833413519140661 8035009080359382517419437)
    ·
      refine ⟨3013128405134768444032289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8035009080359382517419437 3013128405134768444032289)
      ·
        refine ⟨2259846303851076333024217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3013128405134768444032289 2259846303851076333024217)
        ·
          refine ⟨1694884727888307249768163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2259846303851076333024217 1694884727888307249768163)
          ·
            refine ⟨2542327091832460874652245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694884727888307249768163 2542327091832460874652245)
            ·
              refine ⟨29792895607411650874831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2542327091832460874652245 29792895607411650874831)
              ·
                rfl

theorem cell22_2349869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 8].length) (baseStart_2349869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349869 prefixEnd_2349869 := by exact prefixLift 2349869
  have htrace : WordTrace (prefixWord ++ tailWord_2349869) baseStart_2349869 baseEnd_2349869 := by
    simpa [prefixWord, tailWord_2349869, baseEnd_2349869] using wordTrace_append hprefix tailTrace_2349869
  have hstable : (prefixWord ++ tailWord_2349869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349869).length < 2 ^ (prefixWord ++ tailWord_2349869).sum := by decide
  have hdescent : baseEnd_2349869 < baseStart_2349869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349897 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 5]
def baseStart_2349897 : Nat := 118140960795 + 2349897 * 2 ^ 59
def prefixEnd_2349897 : Nat := 4983230072969 + 3 ^ 40 * 2349897 * 2
def baseEnd_2349897 : Nat := 268139255457443944640117

theorem tailTrace_2349897 : CollatzResearch.WordTrace tailWord_2349897 prefixEnd_2349897 268139255457443944640117 := by
  unfold tailWord_2349897
  simp only [CollatzResearch.WordTrace]
  refine ⟨85707784767731974301159945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57138523178487982867439963 85707784767731974301159945)
  ·
    refine ⟨64280838575798980725869959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85707784767731974301159945 64280838575798980725869959)
    ·
      refine ⟨96421257863698471088804939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64280838575798980725869959 96421257863698471088804939)
      ·
        refine ⟨144631886795547706633207409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96421257863698471088804939 144631886795547706633207409)
        ·
          refine ⟨108473915096660779974905557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144631886795547706633207409 108473915096660779974905557)
          ·
            refine ⟨2542357385077987030661849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 108473915096660779974905557 2542357385077987030661849)
            ·
              refine ⟨1906768038808490272996387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542357385077987030661849 1906768038808490272996387)
              ·
                refine ⟨2860152058212735409494581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1906768038808490272996387 2860152058212735409494581)
                ·
                  refine ⟨268139255457443944640117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2860152058212735409494581 268139255457443944640117)
                  ·
                    rfl

theorem cell22_2349897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 5].length) (baseStart_2349897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349897 prefixEnd_2349897 := by exact prefixLift 2349897
  have htrace : WordTrace (prefixWord ++ tailWord_2349897) baseStart_2349897 baseEnd_2349897 := by
    simpa [prefixWord, tailWord_2349897, baseEnd_2349897] using wordTrace_append hprefix tailTrace_2349897
  have hstable : (prefixWord ++ tailWord_2349897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349897).length < 2 ^ (prefixWord ++ tailWord_2349897).sum := by decide
  have hdescent : baseEnd_2349897 < baseStart_2349897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349957 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_2349957 : Nat := 118140960795 + 2349957 * 2 ^ 59
def prefixEnd_2349957 : Nat := 4983230072969 + 3 ^ 40 * 2349957 * 2
def baseEnd_2349957 : Nat := 804438305598511677420167

theorem tailTrace_2349957 : CollatzResearch.WordTrace tailWord_2349957 prefixEnd_2349957 804438305598511677420167 := by
  unfold tailWord_2349957
  simp only [CollatzResearch.WordTrace]
  refine ⟨85709973147514604548344125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57139982098343069698896083 85709973147514604548344125)
  ·
    refine ⟨32141239930317976705629047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85709973147514604548344125 32141239930317976705629047)
    ·
      refine ⟨48211859895476965058443571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32141239930317976705629047 48211859895476965058443571)
      ·
        refine ⟨72317789843215447587665357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48211859895476965058443571 72317789843215447587665357)
        ·
          refine ⟨27119171191205792845374509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72317789843215447587665357 27119171191205792845374509)
          ·
            refine ⟨10169689196702172317015441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27119171191205792845374509 10169689196702172317015441)
            ·
              refine ⟨7627266897526629237761581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10169689196702172317015441 7627266897526629237761581)
              ·
                refine ⟨2860225086572485964160593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7627266897526629237761581 2860225086572485964160593)
                ·
                  refine ⟨2145168814929364473120445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2860225086572485964160593 2145168814929364473120445)
                  ·
                    refine ⟨804438305598511677420167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145168814929364473120445 804438305598511677420167)
                    ·
                      rfl

theorem cell22_2349957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_2349957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349957 prefixEnd_2349957 := by exact prefixLift 2349957
  have htrace : WordTrace (prefixWord ++ tailWord_2349957) baseStart_2349957 baseEnd_2349957 := by
    simpa [prefixWord, tailWord_2349957, baseEnd_2349957] using wordTrace_append hprefix tailTrace_2349957
  have hstable : (prefixWord ++ tailWord_2349957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349957).length < 2 ^ (prefixWord ++ tailWord_2349957).sum := by decide
  have hdescent : baseEnd_2349957 < baseStart_2349957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2349991 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2349991 : Nat := 118140960795 + 2349991 * 2 ^ 59
def prefixEnd_2349991 : Nat := 4983230072969 + 3 ^ 40 * 2349991 * 2
def baseEnd_2349991 : Nat := 804449944493346922070063

theorem tailTrace_2349991 : CollatzResearch.WordTrace tailWord_2349991 prefixEnd_2349991 804449944493346922070063 := by
  unfold tailWord_2349991
  simp only [CollatzResearch.WordTrace]
  refine ⟨85711213229391428355081827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57140808819594285570054551 85711213229391428355081827)
  ·
    refine ⟨128566819844087142532622741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85711213229391428355081827 128566819844087142532622741)
    ·
      refine ⟨6026569680191584806216691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128566819844087142532622741 6026569680191584806216691)
      ·
        refine ⟨9039854520287377209325037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6026569680191584806216691 9039854520287377209325037)
        ·
          refine ⟨3389945445107766453496889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9039854520287377209325037 3389945445107766453496889)
          ·
            refine ⟨2542459083830824840122667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3389945445107766453496889 2542459083830824840122667)
            ·
              refine ⟨3813688625746237260184001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542459083830824840122667 3813688625746237260184001)
              ·
                refine ⟨2860266469309677945138001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3813688625746237260184001 2860266469309677945138001)
                ·
                  refine ⟨2145199851982258458853501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2860266469309677945138001 2145199851982258458853501)
                  ·
                    refine ⟨804449944493346922070063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145199851982258458853501 804449944493346922070063)
                    ·
                      rfl

theorem cell22_2349991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2349991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2349991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2349991 prefixEnd_2349991 := by exact prefixLift 2349991
  have htrace : WordTrace (prefixWord ++ tailWord_2349991) baseStart_2349991 baseEnd_2349991 := by
    simpa [prefixWord, tailWord_2349991, baseEnd_2349991] using wordTrace_append hprefix tailTrace_2349991
  have hstable : (prefixWord ++ tailWord_2349991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2349991).length < 2 ^ (prefixWord ++ tailWord_2349991).sum := by decide
  have hdescent : baseEnd_2349991 < baseStart_2349991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2349991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350036 : List Nat := [2, 4, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_2350036 : Nat := 118140960795 + 2350036 * 2 ^ 59
def prefixEnd_2350036 : Nat := 4983230072969 + 3 ^ 40 * 2350036 * 2
def baseEnd_2350036 : Nat := 804465348912981804694925

theorem tailTrace_2350036 : CollatzResearch.WordTrace tailWord_2350036 prefixEnd_2350036 804465348912981804694925 := by
  unfold tailWord_2350036
  simp only [CollatzResearch.WordTrace]
  refine ⟨42856427257114200520234981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57141903009485600693646641 42856427257114200520234981)
  ·
    refine ⟨8035580110708912597544059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42856427257114200520234981 8035580110708912597544059)
    ·
      refine ⟨12053370166063368896316089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8035580110708912597544059 12053370166063368896316089)
      ·
        refine ⟨9040027624547526672237067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12053370166063368896316089 9040027624547526672237067)
        ·
          refine ⟨13560041436821290008355601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9040027624547526672237067 13560041436821290008355601)
          ·
            refine ⟨10170031077615967506266701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13560041436821290008355601 10170031077615967506266701)
            ·
              refine ⟨3813761654105987814850013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10170031077615967506266701 3813761654105987814850013)
              ·
                refine ⟨1430160620289745430568755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3813761654105987814850013 1430160620289745430568755)
                ·
                  refine ⟨2145240930434618145853133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430160620289745430568755 2145240930434618145853133)
                  ·
                    refine ⟨804465348912981804694925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145240930434618145853133 804465348912981804694925)
                    ·
                      rfl

theorem cell22_2350036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_2350036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350036 prefixEnd_2350036 := by exact prefixLift 2350036
  have htrace : WordTrace (prefixWord ++ tailWord_2350036) baseStart_2350036 baseEnd_2350036 := by
    simpa [prefixWord, tailWord_2350036, baseEnd_2350036] using wordTrace_append hprefix tailTrace_2350036
  have hstable : (prefixWord ++ tailWord_2350036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350036).length < 2 ^ (prefixWord ++ tailWord_2350036).sum := by decide
  have hdescent : baseEnd_2350036 < baseStart_2350036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350053 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 3, 3]
def baseStart_2350053 : Nat := 118140960795 + 2350053 * 2 ^ 59
def prefixEnd_2350053 : Nat := 4983230072969 + 3 ^ 40 * 2350053 * 2
def baseEnd_2350053 : Nat := 804471168360399427019873

theorem tailTrace_2350053 : CollatzResearch.WordTrace tailWord_2350053 prefixEnd_2350053 804471168360399427019873 := by
  unfold tailWord_2350053
  simp only [CollatzResearch.WordTrace]
  refine ⟨85713474555166812943838813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57142316370111208629225875 85713474555166812943838813)
  ·
    refine ⟨32142552958187554853939555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85713474555166812943838813 32142552958187554853939555)
    ·
      refine ⟨48213829437281332280909333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32142552958187554853939555 48213829437281332280909333)
      ·
        refine ⟨2260023254872562450667625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48213829437281332280909333 2260023254872562450667625)
        ·
          refine ⟨1695017441154421838000719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260023254872562450667625 1695017441154421838000719)
          ·
            refine ⟨2542526161731632757001079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695017441154421838000719 2542526161731632757001079)
            ·
              refine ⟨3813789242597449135501619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2542526161731632757001079 3813789242597449135501619)
              ·
                refine ⟨5720683863896173703252429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3813789242597449135501619 5720683863896173703252429)
                ·
                  refine ⟨2145256448961065138719661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5720683863896173703252429 2145256448961065138719661)
                  ·
                    refine ⟨804471168360399427019873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145256448961065138719661 804471168360399427019873)
                    ·
                      rfl

theorem cell22_2350053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_2350053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350053 prefixEnd_2350053 := by exact prefixLift 2350053
  have htrace : WordTrace (prefixWord ++ tailWord_2350053) baseStart_2350053 baseEnd_2350053 := by
    simpa [prefixWord, tailWord_2350053, baseEnd_2350053] using wordTrace_append hprefix tailTrace_2350053
  have hstable : (prefixWord ++ tailWord_2350053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350053).length < 2 ^ (prefixWord ++ tailWord_2350053).sum := by decide
  have hdescent : baseEnd_2350053 < baseStart_2350053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350075 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 1, 5]
def baseStart_2350075 : Nat := 118140960795 + 2350075 * 2 ^ 59
def prefixEnd_2350075 : Nat := 4983230072969 + 3 ^ 40 * 2350075 * 2
def baseEnd_2350075 : Nat := 804478699409998702969805

theorem tailTrace_2350075 : CollatzResearch.WordTrace tailWord_2350075 prefixEnd_2350075 804478699409998702969805 := by
  unfold tailWord_2350075
  simp only [CollatzResearch.WordTrace]
  refine ⟨85714276961087110701139679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57142851307391407134093119 85714276961087110701139679)
  ·
    refine ⟨128571415441630666051709519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85714276961087110701139679 128571415441630666051709519)
    ·
      refine ⟨192857123162445999077564279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128571415441630666051709519 192857123162445999077564279)
      ·
        refine ⟨289285684743668998616346419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192857123162445999077564279 289285684743668998616346419)
        ·
          refine ⟨433928527115503497924519629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289285684743668998616346419 433928527115503497924519629)
          ·
            refine ⟨162723197668313811721694861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 433928527115503497924519629 162723197668313811721694861)
            ·
              refine ⟨61021199125617679395635573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162723197668313811721694861 61021199125617679395635573)
              ·
                refine ⟨5720737418026657443340835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61021199125617679395635573 5720737418026657443340835)
                ·
                  refine ⟨8581106127039986165011253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5720737418026657443340835 8581106127039986165011253)
                  ·
                    refine ⟨804478699409998702969805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8581106127039986165011253 804478699409998702969805)
                    ·
                      rfl

theorem cell22_2350075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 5].length) (baseStart_2350075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350075 prefixEnd_2350075 := by exact prefixLift 2350075
  have htrace : WordTrace (prefixWord ++ tailWord_2350075) baseStart_2350075 baseEnd_2350075 := by
    simpa [prefixWord, tailWord_2350075, baseEnd_2350075] using wordTrace_append hprefix tailTrace_2350075
  have hstable : (prefixWord ++ tailWord_2350075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350075).length < 2 ^ (prefixWord ++ tailWord_2350075).sum := by decide
  have hdescent : baseEnd_2350075 < baseStart_2350075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350092 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_2350092 : Nat := 118140960795 + 2350092 * 2 ^ 59
def prefixEnd_2350092 : Nat := 4983230072969 + 3 ^ 40 * 2350092 * 2
def baseEnd_2350092 : Nat := 804484518857416325294753

theorem tailTrace_2350092 : CollatzResearch.WordTrace tailWord_2350092 prefixEnd_2350092 804484518857416325294753 := by
  unfold tailWord_2350092
  simp only [CollatzResearch.WordTrace]
  refine ⟨42857448501012761302254265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57143264668017015069672353 42857448501012761302254265)
  ·
    refine ⟨32143086375759570976690699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42857448501012761302254265 32143086375759570976690699)
    ·
      refine ⟨48214629563639356465036049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32143086375759570976690699 48214629563639356465036049)
      ·
        refine ⟨36160972172729517348777037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48214629563639356465036049 36160972172729517348777037)
        ·
          refine ⟨13560364564773569005791389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36160972172729517348777037 13560364564773569005791389)
          ·
            refine ⟨5085136711790088377171771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13560364564773569005791389 5085136711790088377171771)
            ·
              refine ⟨7627705067685132565757657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5085136711790088377171771 7627705067685132565757657)
              ·
                refine ⟨5720778800763849424318243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7627705067685132565757657 5720778800763849424318243)
                ·
                  refine ⟨8581168201145774136477365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5720778800763849424318243 8581168201145774136477365)
                  ·
                    refine ⟨804484518857416325294753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8581168201145774136477365 804484518857416325294753)
                    ·
                      rfl

theorem cell22_2350092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_2350092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350092 prefixEnd_2350092 := by exact prefixLift 2350092
  have htrace : WordTrace (prefixWord ++ tailWord_2350092) baseStart_2350092 baseEnd_2350092 := by
    simpa [prefixWord, tailWord_2350092, baseEnd_2350092] using wordTrace_append hprefix tailTrace_2350092
  have hstable : (prefixWord ++ tailWord_2350092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350092).length < 2 ^ (prefixWord ++ tailWord_2350092).sum := by decide
  have hdescent : baseEnd_2350092 < baseStart_2350092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350111 : List Nat := [1, 1, 2, 4, 1, 5, 2, 2, 4]
def baseStart_2350111 : Nat := 118140960795 + 2350111 * 2 ^ 59
def prefixEnd_2350111 : Nat := 4983230072969 + 3 ^ 40 * 2350111 * 2
def baseEnd_2350111 : Nat := 268163674315235536356565

theorem tailTrace_2350111 : CollatzResearch.WordTrace tailWord_2350111 prefixEnd_2350111 268163674315235536356565 := by
  unfold tailWord_2350111
  simp only [CollatzResearch.WordTrace]
  refine ⟨85715589988956688849450187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57143726659304459232966791 85715589988956688849450187)
  ·
    refine ⟨128573384983435033274175281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85715589988956688849450187 128573384983435033274175281)
    ·
      refine ⟨96430038737576274955631461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128573384983435033274175281 96430038737576274955631461)
      ·
        refine ⟨18080632263295551554180899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96430038737576274955631461 18080632263295551554180899)
        ·
          refine ⟨27120948394943327331271349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18080632263295551554180899 27120948394943327331271349)
          ·
            refine ⟨2542588912025936937306689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27120948394943327331271349 2542588912025936937306689)
            ·
              refine ⟨1906941684019452702980017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2542588912025936937306689 1906941684019452702980017)
              ·
                refine ⟨1430206263014589527235013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1906941684019452702980017 1430206263014589527235013)
                ·
                  refine ⟨268163674315235536356565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430206263014589527235013 268163674315235536356565)
                  ·
                    rfl

theorem cell22_2350111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 4].length) (baseStart_2350111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350111 prefixEnd_2350111 := by exact prefixLift 2350111
  have htrace : WordTrace (prefixWord ++ tailWord_2350111) baseStart_2350111 baseEnd_2350111 := by
    simpa [prefixWord, tailWord_2350111, baseEnd_2350111] using wordTrace_append hprefix tailTrace_2350111
  have hstable : (prefixWord ++ tailWord_2350111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350111).length < 2 ^ (prefixWord ++ tailWord_2350111).sum := by decide
  have hdescent : baseEnd_2350111 < baseStart_2350111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350135 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 4, 6]
def baseStart_2350135 : Nat := 118140960795 + 2350135 * 2 ^ 59
def prefixEnd_2350135 : Nat := 4983230072969 + 3 ^ 40 * 2350135 * 2
def baseEnd_2350135 : Nat := 804499238636178546469621

theorem tailTrace_2350135 : CollatzResearch.WordTrace tailWord_2350135 prefixEnd_2350135 804499238636178546469621 := by
  unfold tailWord_2350135
  simp only [CollatzResearch.WordTrace]
  refine ⟨85716465340869740948323859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57144310227246493965549239 85716465340869740948323859)
  ·
    refine ⟨128574698011304611422485789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85716465340869740948323859 128574698011304611422485789)
    ·
      refine ⟨48215511754239229283432171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128574698011304611422485789 48215511754239229283432171)
      ·
        refine ⟨72323267631358843925148257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48215511754239229283432171 72323267631358843925148257)
        ·
          refine ⟨54242450723519132943861193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72323267631358843925148257 54242450723519132943861193)
          ·
            refine ⟨40681838042639349707895895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54242450723519132943861193 40681838042639349707895895)
            ·
              refine ⟨61022757063959024561843843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40681838042639349707895895 61022757063959024561843843)
              ·
                refine ⟨91534135595938536842765765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61022757063959024561843843 91534135595938536842765765)
                ·
                  refine ⟨17162650424238475658018581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91534135595938536842765765 17162650424238475658018581)
                  ·
                    refine ⟨804499238636178546469621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17162650424238475658018581 804499238636178546469621)
                    ·
                      rfl

theorem cell22_2350135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_2350135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350135 prefixEnd_2350135 := by exact prefixLift 2350135
  have htrace : WordTrace (prefixWord ++ tailWord_2350135) baseStart_2350135 baseEnd_2350135 := by
    simpa [prefixWord, tailWord_2350135, baseEnd_2350135] using wordTrace_append hprefix tailTrace_2350135
  have hstable : (prefixWord ++ tailWord_2350135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350135).length < 2 ^ (prefixWord ++ tailWord_2350135).sum := by decide
  have hdescent : baseEnd_2350135 < baseStart_2350135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350289 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 3, 3]
def baseStart_2350289 : Nat := 118140960795 + 2350289 * 2 ^ 59
def prefixEnd_2350289 : Nat := 4983230072969 + 3 ^ 40 * 2350289 * 2
def baseEnd_2350289 : Nat := 804551955983373478119149

theorem tailTrace_2350289 : CollatzResearch.WordTrace tailWord_2350289 prefixEnd_2350289 804551955983373478119149 := by
  unfold tailWord_2350289
  simp only [CollatzResearch.WordTrace]
  refine ⟨85722082182311825249429921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57148054788207883499619947 85722082182311825249429921)
  ·
    refine ⟨64291561636733868937072441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85722082182311825249429921 64291561636733868937072441)
    ·
      refine ⟨48218671227550401702804331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64291561636733868937072441 48218671227550401702804331)
      ·
        refine ⟨72328006841325602554206497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48218671227550401702804331 72328006841325602554206497)
        ·
          refine ⟨54246005130994201915654873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72328006841325602554206497 54246005130994201915654873)
          ·
            refine ⟨40684503848245651436741155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54246005130994201915654873 40684503848245651436741155)
            ·
              refine ⟨61026755772368477155111733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40684503848245651436741155 61026755772368477155111733)
              ·
                refine ⟨5721258353659544733291725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61026755772368477155111733 5721258353659544733291725)
                ·
                  refine ⟨2145471882622329274984397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5721258353659544733291725 2145471882622329274984397)
                  ·
                    refine ⟨804551955983373478119149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145471882622329274984397 804551955983373478119149)
                    ·
                      rfl

theorem cell22_2350289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_2350289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350289 prefixEnd_2350289 := by exact prefixLift 2350289
  have htrace : WordTrace (prefixWord ++ tailWord_2350289) baseStart_2350289 baseEnd_2350289 := by
    simpa [prefixWord, tailWord_2350289, baseEnd_2350289] using wordTrace_append hprefix tailTrace_2350289
  have hstable : (prefixWord ++ tailWord_2350289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350289).length < 2 ^ (prefixWord ++ tailWord_2350289).sum := by decide
  have hdescent : baseEnd_2350289 < baseStart_2350289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350323 : List Nat := [1, 1, 1, 2, 2, 6, 2, 3, 1, 3]
def baseStart_2350323 : Nat := 118140960795 + 2350323 * 2 ^ 59
def prefixEnd_2350323 : Nat := 4983230072969 + 3 ^ 40 * 2350323 * 2
def baseEnd_2350323 : Nat := 804563594878208722769045

theorem tailTrace_2350323 : CollatzResearch.WordTrace tailWord_2350323 prefixEnd_2350323 804563594878208722769045 := by
  unfold tailWord_2350323
  simp only [CollatzResearch.WordTrace]
  refine ⟨85723322264188649056167623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57148881509459099370778415 85723322264188649056167623)
  ·
    refine ⟨128584983396282973584251435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85723322264188649056167623 128584983396282973584251435)
    ·
      refine ⟨192877475094424460376377153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128584983396282973584251435 192877475094424460376377153)
      ·
        refine ⟨144658106320818345282282865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192877475094424460376377153 144658106320818345282282865)
        ·
          refine ⟨108493579740613758961712149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144658106320818345282282865 108493579740613758961712149)
          ·
            refine ⟨5085636550341269951330257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108493579740613758961712149 5085636550341269951330257)
            ·
              refine ⟨3814227412755952463497693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5085636550341269951330257 3814227412755952463497693)
              ·
                refine ⟨1430335279783482173811635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3814227412755952463497693 1430335279783482173811635)
                ·
                  refine ⟨2145502919675223260717453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430335279783482173811635 2145502919675223260717453)
                  ·
                    refine ⟨804563594878208722769045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145502919675223260717453 804563594878208722769045)
                    ·
                      rfl

theorem cell22_2350323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 1, 3].length) (baseStart_2350323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350323 prefixEnd_2350323 := by exact prefixLift 2350323
  have htrace : WordTrace (prefixWord ++ tailWord_2350323) baseStart_2350323 baseEnd_2350323 := by
    simpa [prefixWord, tailWord_2350323, baseEnd_2350323] using wordTrace_append hprefix tailTrace_2350323
  have hstable : (prefixWord ++ tailWord_2350323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350323).length < 2 ^ (prefixWord ++ tailWord_2350323).sum := by decide
  have hdescent : baseEnd_2350323 < baseStart_2350323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350364 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 6]
def baseStart_2350364 : Nat := 118140960795 + 2350364 * 2 ^ 59
def prefixEnd_2350364 : Nat := 4983230072969 + 3 ^ 40 * 2350364 * 2
def baseEnd_2350364 : Nat := 268192543338699427497973

theorem tailTrace_2350364 : CollatzResearch.WordTrace tailWord_2350364 prefixEnd_2350364 268192543338699427497973 := by
  unfold tailWord_2350364
  simp only [CollatzResearch.WordTrace]
  refine ⟨42862408828520056529205073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57149878438026742038940097 42862408828520056529205073)
  ·
    refine ⟨32146806621390042396903805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42862408828520056529205073 32146806621390042396903805)
    ·
      refine ⟨12055052483021265898838927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32146806621390042396903805 12055052483021265898838927)
      ·
        refine ⟨18082578724531898848258391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12055052483021265898838927 18082578724531898848258391)
        ·
          refine ⟨27123868086797848272387587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18082578724531898848258391 27123868086797848272387587)
          ·
            refine ⟨40685802130196772408581381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27123868086797848272387587 40685802130196772408581381)
            ·
              refine ⟨7628587899411894826609009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40685802130196772408581381 7628587899411894826609009)
              ·
                refine ⟨5721440924558921119956757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7628587899411894826609009 5721440924558921119956757)
                ·
                  refine ⟨268192543338699427497973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5721440924558921119956757 268192543338699427497973)
                  ·
                    rfl

theorem cell22_2350364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_2350364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350364 prefixEnd_2350364 := by exact prefixLift 2350364
  have htrace : WordTrace (prefixWord ++ tailWord_2350364) baseStart_2350364 baseEnd_2350364 := by
    simpa [prefixWord, tailWord_2350364, baseEnd_2350364] using wordTrace_append hprefix tailTrace_2350364
  have hstable : (prefixWord ++ tailWord_2350364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350364).length < 2 ^ (prefixWord ++ tailWord_2350364).sum := by decide
  have hdescent : baseEnd_2350364 < baseStart_2350364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350396 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_2350396 : Nat := 118140960795 + 2350396 * 2 ^ 59
def prefixEnd_2350396 : Nat := 4983230072969 + 3 ^ 40 * 2350396 * 2
def baseEnd_2350396 : Nat := 804588584270060865693821

theorem tailTrace_2350396 : CollatzResearch.WordTrace tailWord_2350396 prefixEnd_2350396 804588584270060865693821 := by
  unfold tailWord_2350396
  simp only [CollatzResearch.WordTrace]
  refine ⟨42862992396462091261787521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57150656528616121682383361 42862992396462091261787521)
  ·
    refine ⟨32147244297346568446340641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42862992396462091261787521 32147244297346568446340641)
    ·
      refine ⟨24110433223009926334755481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32147244297346568446340641 24110433223009926334755481)
      ·
        refine ⟨18082824917257444751066611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24110433223009926334755481 18082824917257444751066611)
        ·
          refine ⟨27124237375886167126599917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18082824917257444751066611 27124237375886167126599917)
          ·
            refine ⟨10171589015957312672474969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27124237375886167126599917 10171589015957312672474969)
            ·
              refine ⟨7628691761967984504356227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10171589015957312672474969 7628691761967984504356227)
              ·
                refine ⟨11443037642951976756534341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7628691761967984504356227 11443037642951976756534341)
                ·
                  refine ⟨2145569558053495641850189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11443037642951976756534341 2145569558053495641850189)
                  ·
                    refine ⟨804588584270060865693821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145569558053495641850189 804588584270060865693821)
                    ·
                      rfl

theorem cell22_2350396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_2350396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350396 prefixEnd_2350396 := by exact prefixLift 2350396
  have htrace : WordTrace (prefixWord ++ tailWord_2350396) baseStart_2350396 baseEnd_2350396 := by
    simpa [prefixWord, tailWord_2350396, baseEnd_2350396] using wordTrace_append hprefix tailTrace_2350396
  have hstable : (prefixWord ++ tailWord_2350396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350396).length < 2 ^ (prefixWord ++ tailWord_2350396).sum := by decide
  have hdescent : baseEnd_2350396 < baseStart_2350396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350458 : List Nat := [3, 1, 1, 1, 1, 1, 2, 8, 1, 3]
def baseStart_2350458 : Nat := 118140960795 + 2350458 * 2 ^ 59
def prefixEnd_2350458 : Nat := 4983230072969 + 3 ^ 40 * 2350458 * 2
def baseEnd_2350458 : Nat := 804609808137113370643631

theorem tailTrace_2350458 : CollatzResearch.WordTrace tailWord_2350458 prefixEnd_2350458 804609808137113370643631 := by
  unfold tailWord_2350458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21432061529674891778083007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57152164079133044741554685 21432061529674891778083007)
  ·
    refine ⟨32148092294512337667124511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21432061529674891778083007 32148092294512337667124511)
    ·
      refine ⟨48222138441768506500686767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32148092294512337667124511 48222138441768506500686767)
      ·
        refine ⟨72333207662652759751030151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48222138441768506500686767 72333207662652759751030151)
        ·
          refine ⟨108499811493979139626545227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72333207662652759751030151 108499811493979139626545227)
          ·
            refine ⟨162749717240968709439817841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108499811493979139626545227 162749717240968709439817841)
            ·
              refine ⟨122062287930726532079863381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162749717240968709439817841 122062287930726532079863381)
              ·
                refine ⟨1430417436688201547810899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 122062287930726532079863381 1430417436688201547810899)
                ·
                  refine ⟨2145626155032302321716349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430417436688201547810899 2145626155032302321716349)
                  ·
                    refine ⟨804609808137113370643631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145626155032302321716349 804609808137113370643631)
                    ·
                      rfl

theorem cell22_2350458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_2350458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350458 prefixEnd_2350458 := by exact prefixLift 2350458
  have htrace : WordTrace (prefixWord ++ tailWord_2350458) baseStart_2350458 baseEnd_2350458 := by
    simpa [prefixWord, tailWord_2350458, baseEnd_2350458] using wordTrace_append hprefix tailTrace_2350458
  have hstable : (prefixWord ++ tailWord_2350458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350458).length < 2 ^ (prefixWord ++ tailWord_2350458).sum := by decide
  have hdescent : baseEnd_2350458 < baseStart_2350458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350469 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_2350469 : Nat := 118140960795 + 2350469 * 2 ^ 59
def prefixEnd_2350469 : Nat := 4983230072969 + 3 ^ 40 * 2350469 * 2
def baseEnd_2350469 : Nat := 804613573661913008618597

theorem tailTrace_2350469 : CollatzResearch.WordTrace tailWord_2350469 prefixEnd_2350469 804613573661913008618597 := by
  unfold tailWord_2350469
  simp only [CollatzResearch.WordTrace]
  refine ⟨85728647321659715990982461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57152431547773143993988307 85728647321659715990982461)
  ·
    refine ⟨32148242745622393496618423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85728647321659715990982461 32148242745622393496618423)
    ·
      refine ⟨48222364118433590244927635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32148242745622393496618423 48222364118433590244927635)
      ·
        refine ⟨72333546177650385367391453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48222364118433590244927635 72333546177650385367391453)
        ·
          refine ⟨27125079816618894512771795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72333546177650385367391453 27125079816618894512771795)
          ·
            refine ⟨40687619724928341769157693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27125079816618894512771795 40687619724928341769157693)
            ·
              refine ⟨15257857396848128163434135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40687619724928341769157693 15257857396848128163434135)
              ·
                refine ⟨22886786095272192245151203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15257857396848128163434135 22886786095272192245151203)
                ·
                  refine ⟨34330179142908288367726805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22886786095272192245151203 34330179142908288367726805)
                  ·
                    refine ⟨804613573661913008618597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34330179142908288367726805 804613573661913008618597)
                    ·
                      rfl

theorem cell22_2350469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_2350469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350469 prefixEnd_2350469 := by exact prefixLift 2350469
  have htrace : WordTrace (prefixWord ++ tailWord_2350469) baseStart_2350469 baseEnd_2350469 := by
    simpa [prefixWord, tailWord_2350469, baseEnd_2350469] using wordTrace_append hprefix tailTrace_2350469
  have hstable : (prefixWord ++ tailWord_2350469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350469).length < 2 ^ (prefixWord ++ tailWord_2350469).sum := by decide
  have hdescent : baseEnd_2350469 < baseStart_2350469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350471 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 5]
def baseStart_2350471 : Nat := 118140960795 + 2350471 * 2 ^ 59
def prefixEnd_2350471 : Nat := 4983230072969 + 3 ^ 40 * 2350471 * 2
def baseEnd_2350471 : Nat := 268204752767595223356197

theorem tailTrace_2350471 : CollatzResearch.WordTrace tailWord_2350471 prefixEnd_2350471 268204752767595223356197 := by
  unfold tailWord_2350471
  simp only [CollatzResearch.WordTrace]
  refine ⟨85728720267652470332555267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57152480178434980221703511 85728720267652470332555267)
  ·
    refine ⟨128593080401478705498832901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85728720267652470332555267 128593080401478705498832901)
    ·
      refine ⟨24111202575277257281031169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128593080401478705498832901 24111202575277257281031169)
      ·
        refine ⟨18083401931457942960773377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24111202575277257281031169 18083401931457942960773377)
        ·
          refine ⟨13562551448593457220580033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18083401931457942960773377 13562551448593457220580033)
          ·
            refine ⟨10171913586445092915435025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13562551448593457220580033 10171913586445092915435025)
            ·
              refine ⟨7628935189833819686576269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10171913586445092915435025 7628935189833819686576269)
              ·
                refine ⟨2860850696187682382466101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7628935189833819686576269 2860850696187682382466101)
                ·
                  refine ⟨268204752767595223356197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2860850696187682382466101 268204752767595223356197)
                  ·
                    rfl

theorem cell22_2350471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 5].length) (baseStart_2350471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350471 prefixEnd_2350471 := by exact prefixLift 2350471
  have htrace : WordTrace (prefixWord ++ tailWord_2350471) baseStart_2350471 baseEnd_2350471 := by
    simpa [prefixWord, tailWord_2350471, baseEnd_2350471] using wordTrace_append hprefix tailTrace_2350471
  have hstable : (prefixWord ++ tailWord_2350471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350471).length < 2 ^ (prefixWord ++ tailWord_2350471).sum := by decide
  have hdescent : baseEnd_2350471 < baseStart_2350471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350499 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 8]
def baseStart_2350499 : Nat := 118140960795 + 2350499 * 2 ^ 59
def prefixEnd_2350499 : Nat := 4983230072969 + 3 ^ 40 * 2350499 * 2
def baseEnd_2350499 : Nat := 268207947758334310122835

theorem tailTrace_2350499 : CollatzResearch.WordTrace tailWord_2350499 prefixEnd_2350499 268207947758334310122835 := by
  unfold tailWord_2350499
  simp only [CollatzResearch.WordTrace]
  refine ⟨85729741511551031114574551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57153161007700687409716367 85729741511551031114574551)
  ·
    refine ⟨128594612267326546671861827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85729741511551031114574551 128594612267326546671861827)
    ·
      refine ⟨192891918400989820007792741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128594612267326546671861827 192891918400989820007792741)
      ·
        refine ⟨36167234700185591251461139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192891918400989820007792741 36167234700185591251461139)
        ·
          refine ⟨54250852050278386877191709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36167234700185591251461139 54250852050278386877191709)
          ·
            refine ⟨20344069518854395078946891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54250852050278386877191709 20344069518854395078946891)
            ·
              refine ⟨30516104278281592618420337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20344069518854395078946891 30516104278281592618420337)
              ·
                refine ⟨22887078208711194463815253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30516104278281592618420337 22887078208711194463815253)
                ·
                  refine ⟨268207947758334310122835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22887078208711194463815253 268207947758334310122835)
                  ·
                    rfl

theorem cell22_2350499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 8].length) (baseStart_2350499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350499 prefixEnd_2350499 := by exact prefixLift 2350499
  have htrace : WordTrace (prefixWord ++ tailWord_2350499) baseStart_2350499 baseEnd_2350499 := by
    simpa [prefixWord, tailWord_2350499, baseEnd_2350499] using wordTrace_append hprefix tailTrace_2350499
  have hstable : (prefixWord ++ tailWord_2350499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350499).length < 2 ^ (prefixWord ++ tailWord_2350499).sum := by decide
  have hdescent : baseEnd_2350499 < baseStart_2350499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350531 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 1, 5]
def baseStart_2350531 : Nat := 118140960795 + 2350531 * 2 ^ 59
def prefixEnd_2350531 : Nat := 4983230072969 + 3 ^ 40 * 2350531 * 2
def baseEnd_2350531 : Nat := 804634797528965513568407

theorem tailTrace_2350531 : CollatzResearch.WordTrace tailWord_2350531 prefixEnd_2350531 804634797528965513568407 := by
  unfold tailWord_2350531
  simp only [CollatzResearch.WordTrace]
  refine ⟨85730908647435100579739447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57153939098290067053159631 85730908647435100579739447)
  ·
    refine ⟨128596362971152650869609171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85730908647435100579739447 128596362971152650869609171)
    ·
      refine ⟨192894544456728976304413757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128596362971152650869609171 192894544456728976304413757)
      ·
        refine ⟨72335454171273366114155159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192894544456728976304413757 72335454171273366114155159)
        ·
          refine ⟨108503181256910049171232739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72335454171273366114155159 108503181256910049171232739)
          ·
            refine ⟨162754771885365073756849109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108503181256910049171232739 162754771885365073756849109)
            ·
              refine ⟨3814564966063243916176151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 162754771885365073756849109 3814564966063243916176151)
              ·
                refine ⟨5721847449094865874264227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3814564966063243916176151 5721847449094865874264227)
                ·
                  refine ⟨8582771173642298811396341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5721847449094865874264227 8582771173642298811396341)
                  ·
                    refine ⟨804634797528965513568407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8582771173642298811396341 804634797528965513568407)
                    ·
                      rfl

theorem cell22_2350531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 5].length) (baseStart_2350531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350531 prefixEnd_2350531 := by exact prefixLift 2350531
  have htrace : WordTrace (prefixWord ++ tailWord_2350531) baseStart_2350531 baseEnd_2350531 := by
    simpa [prefixWord, tailWord_2350531, baseEnd_2350531] using wordTrace_append hprefix tailTrace_2350531
  have hstable : (prefixWord ++ tailWord_2350531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350531).length < 2 ^ (prefixWord ++ tailWord_2350531).sum := by decide
  have hdescent : baseEnd_2350531 < baseStart_2350531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350544 : List Nat := [2, 1, 1, 1, 1, 2, 2, 12]
def baseStart_2350544 : Nat := 118140960795 + 2350544 * 2 ^ 59
def prefixEnd_2350544 : Nat := 4983230072969 + 3 ^ 40 * 2350544 * 2
def baseEnd_2350544 : Nat := 89404360854959756999263

theorem tailTrace_2350544 : CollatzResearch.WordTrace tailWord_2350544 prefixEnd_2350544 89404360854959756999263 := by
  unfold tailWord_2350544
  simp only [CollatzResearch.WordTrace]
  refine ⟨42865691398194001899981343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57154255197592002533308457 42865691398194001899981343)
  ·
    refine ⟨64298537097291002849972015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42865691398194001899981343 64298537097291002849972015)
    ·
      refine ⟨96447805645936504274958023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64298537097291002849972015 96447805645936504274958023)
      ·
        refine ⟨144671708468904756412437035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96447805645936504274958023 144671708468904756412437035)
        ·
          refine ⟨217007562703357134618655553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144671708468904756412437035 217007562703357134618655553)
          ·
            refine ⟨162755672027517850963991665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217007562703357134618655553 162755672027517850963991665)
            ·
              refine ⟨122066754020638388222993749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162755672027517850963991665 122066754020638388222993749)
              ·
                refine ⟨89404360854959756999263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 122066754020638388222993749 89404360854959756999263)
                ·
                  rfl

theorem cell22_2350544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 12].length) (baseStart_2350544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350544 prefixEnd_2350544 := by exact prefixLift 2350544
  have htrace : WordTrace (prefixWord ++ tailWord_2350544) baseStart_2350544 baseEnd_2350544 := by
    simpa [prefixWord, tailWord_2350544, baseEnd_2350544] using wordTrace_append hprefix tailTrace_2350544
  have hstable : (prefixWord ++ tailWord_2350544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350544).length < 2 ^ (prefixWord ++ tailWord_2350544).sum := by decide
  have hdescent : baseEnd_2350544 < baseStart_2350544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350561 : List Nat := [1, 2, 3, 1, 2, 5, 8]
def baseStart_2350561 : Nat := 118140960795 + 2350561 * 2 ^ 59
def prefixEnd_2350561 : Nat := 4983230072969 + 3 ^ 40 * 2350561 * 2
def baseEnd_2350561 : Nat := 29801669153409460567345

theorem tailTrace_2350561 : CollatzResearch.WordTrace tailWord_2350561 prefixEnd_2350561 29801669153409460567345 := by
  unfold tailWord_2350561
  simp only [CollatzResearch.WordTrace]
  refine ⟨85732002837326415703331537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57154668558217610468887691 85732002837326415703331537)
  ·
    refine ⟨64299002127994811777498653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85732002837326415703331537 64299002127994811777498653)
    ·
      refine ⟨24112125797998054416561995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64299002127994811777498653 24112125797998054416561995)
      ·
        refine ⟨36168188696997081624842993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24112125797998054416561995 36168188696997081624842993)
        ·
          refine ⟨27126141522747811218632245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36168188696997081624842993 27126141522747811218632245)
          ·
            refine ⟨2543075767757607301746773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27126141522747811218632245 2543075767757607301746773)
            ·
              refine ⟨29801669153409460567345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2543075767757607301746773 29801669153409460567345)
              ·
                rfl

theorem cell22_2350561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 8].length) (baseStart_2350561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350561 prefixEnd_2350561 := by exact prefixLift 2350561
  have htrace : WordTrace (prefixWord ++ tailWord_2350561) baseStart_2350561 baseEnd_2350561 := by
    simpa [prefixWord, tailWord_2350561, baseEnd_2350561] using wordTrace_append hprefix tailTrace_2350561
  have hstable : (prefixWord ++ tailWord_2350561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350561).length < 2 ^ (prefixWord ++ tailWord_2350561).sum := by decide
  have hdescent : baseEnd_2350561 < baseStart_2350561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350563 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 2, 4]
def baseStart_2350563 : Nat := 118140960795 + 2350563 * 2 ^ 59
def prefixEnd_2350563 : Nat := 4983230072969 + 3 ^ 40 * 2350563 * 2
def baseEnd_2350563 : Nat := 804645751782928096768309

theorem tailTrace_2350563 : CollatzResearch.WordTrace tailWord_2350563 prefixEnd_2350563 804645751782928096768309 := by
  unfold tailWord_2350563
  simp only [CollatzResearch.WordTrace]
  refine ⟨85732075783319170044904343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57154717188879446696602895 85732075783319170044904343)
  ·
    refine ⟨128598113674978755067356515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85732075783319170044904343 128598113674978755067356515)
    ·
      refine ⟨192897170512468132601034773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128598113674978755067356515 192897170512468132601034773)
      ·
        refine ⟨9042054867771943715673505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 192897170512468132601034773 9042054867771943715673505)
        ·
          refine ⟨6781541150828957786755129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9042054867771943715673505 6781541150828957786755129)
          ·
            refine ⟨5086155863121718340066347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6781541150828957786755129 5086155863121718340066347)
            ·
              refine ⟨7629233794682577510099521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086155863121718340066347 7629233794682577510099521)
              ·
                refine ⟨5721925346011933132574641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7629233794682577510099521 5721925346011933132574641)
                ·
                  refine ⟨4291444009508949849430981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5721925346011933132574641 4291444009508949849430981)
                  ·
                    refine ⟨804645751782928096768309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4291444009508949849430981 804645751782928096768309)
                    ·
                      rfl

theorem cell22_2350563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 4].length) (baseStart_2350563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350563 prefixEnd_2350563 := by exact prefixLift 2350563
  have htrace : WordTrace (prefixWord ++ tailWord_2350563) baseStart_2350563 baseEnd_2350563 := by
    simpa [prefixWord, tailWord_2350563, baseEnd_2350563] using wordTrace_append hprefix tailTrace_2350563
  have hstable : (prefixWord ++ tailWord_2350563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350563).length < 2 ^ (prefixWord ++ tailWord_2350563).sum := by decide
  have hdescent : baseEnd_2350563 < baseStart_2350563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350578 : List Nat := [3, 2, 1, 4, 1, 2, 2, 7]
def baseStart_2350578 : Nat := 118140960795 + 2350578 * 2 ^ 59
def prefixEnd_2350578 : Nat := 4983230072969 + 3 ^ 40 * 2350578 * 2
def baseEnd_2350578 : Nat := 89405654065497006404807

theorem tailTrace_2350578 : CollatzResearch.WordTrace tailWord_2350578 prefixEnd_2350578 89405654065497006404807 := by
  unfold tailWord_2350578
  simp only [CollatzResearch.WordTrace]
  refine ⟨21433155719566206901675097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57155081918843218404466925 21433155719566206901675097)
  ·
    refine ⟨16074866789674655176256323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21433155719566206901675097 16074866789674655176256323)
    ·
      refine ⟨24112300184511982764384485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16074866789674655176256323 24112300184511982764384485)
      ·
        refine ⟨4521056284595996768322091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24112300184511982764384485 4521056284595996768322091)
        ·
          refine ⟨6781584426893995152483137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4521056284595996768322091 6781584426893995152483137)
          ·
            refine ⟨5086188320170496364362353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6781584426893995152483137 5086188320170496364362353)
            ·
              refine ⟨3814641240127872273271765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5086188320170496364362353 3814641240127872273271765)
              ·
                refine ⟨89405654065497006404807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3814641240127872273271765 89405654065497006404807)
                ·
                  rfl

theorem cell22_2350578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_2350578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350578 prefixEnd_2350578 := by exact prefixLift 2350578
  have htrace : WordTrace (prefixWord ++ tailWord_2350578) baseStart_2350578 baseEnd_2350578 := by
    simpa [prefixWord, tailWord_2350578, baseEnd_2350578] using wordTrace_append hprefix tailTrace_2350578
  have hstable : (prefixWord ++ tailWord_2350578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350578).length < 2 ^ (prefixWord ++ tailWord_2350578).sum := by decide
  have hdescent : baseEnd_2350578 < baseStart_2350578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350582 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_2350582 : Nat := 118140960795 + 2350582 * 2 ^ 59
def prefixEnd_2350582 : Nat := 4983230072969 + 3 ^ 40 * 2350582 * 2
def baseEnd_2350582 : Nat := 804652255871218380543251

theorem tailTrace_2350582 : CollatzResearch.WordTrace tailWord_2350582 prefixEnd_2350582 804652255871218380543251 := by
  unfold tailWord_2350582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5358298048140646018115375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57155179180166890859897333 5358298048140646018115375)
  ·
    refine ⟨8037447072210969027173063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5358298048140646018115375 8037447072210969027173063)
    ·
      refine ⟨12056170608316453540759595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8037447072210969027173063 12056170608316453540759595)
      ·
        refine ⟨18084255912474680311139393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12056170608316453540759595 18084255912474680311139393)
        ·
          refine ⟨13563191934356010233354545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18084255912474680311139393 13563191934356010233354545)
          ·
            refine ⟨10172393950767007675015909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13563191934356010233354545 10172393950767007675015909)
            ·
              refine ⟨1907323865768813939065483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10172393950767007675015909 1907323865768813939065483)
              ·
                refine ⟨2860985798653220908598225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907323865768813939065483 2860985798653220908598225)
                ·
                  refine ⟨2145739348989915681448669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2860985798653220908598225 2145739348989915681448669)
                  ·
                    refine ⟨804652255871218380543251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145739348989915681448669 804652255871218380543251)
                    ·
                      rfl

theorem cell22_2350582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_2350582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350582 prefixEnd_2350582 := by exact prefixLift 2350582
  have htrace : WordTrace (prefixWord ++ tailWord_2350582) baseStart_2350582 baseEnd_2350582 := by
    simpa [prefixWord, tailWord_2350582, baseEnd_2350582] using wordTrace_append hprefix tailTrace_2350582
  have hstable : (prefixWord ++ tailWord_2350582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350582).length < 2 ^ (prefixWord ++ tailWord_2350582).sum := by decide
  have hdescent : baseEnd_2350582 < baseStart_2350582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350627 : List Nat := [1, 1, 1, 4, 5, 1, 1, 4, 1, 3]
def baseStart_2350627 : Nat := 118140960795 + 2350627 * 2 ^ 59
def prefixEnd_2350627 : Nat := 4983230072969 + 3 ^ 40 * 2350627 * 2
def baseEnd_2350627 : Nat := 804667660290853263168113

theorem tailTrace_2350627 : CollatzResearch.WordTrace tailWord_2350627 prefixEnd_2350627 804667660290853263168113 := by
  unfold tailWord_2350627
  simp only [CollatzResearch.WordTrace]
  refine ⟨85734410055087308975234135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57156273370058205983489423 85734410055087308975234135)
  ·
    refine ⟨128601615082630963462851203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85734410055087308975234135 128601615082630963462851203)
    ·
      refine ⟨192902422623946445194276805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128601615082630963462851203 192902422623946445194276805)
      ·
        refine ⟨36169204241989958473926901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192902422623946445194276805 36169204241989958473926901)
        ·
          refine ⟨3390862897686558606930647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36169204241989958473926901 3390862897686558606930647)
          ·
            refine ⟨5086294346529837910395971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3390862897686558606930647 5086294346529837910395971)
            ·
              refine ⟨7629441519794756865593957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086294346529837910395971 7629441519794756865593957)
              ·
                refine ⟨1430520284961516912298867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7629441519794756865593957 1430520284961516912298867)
                ·
                  refine ⟨2145780427442275368448301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1430520284961516912298867 2145780427442275368448301)
                  ·
                    refine ⟨804667660290853263168113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145780427442275368448301 804667660290853263168113)
                    ·
                      rfl

theorem cell22_2350627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 1, 3].length) (baseStart_2350627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350627 prefixEnd_2350627 := by exact prefixLift 2350627
  have htrace : WordTrace (prefixWord ++ tailWord_2350627) baseStart_2350627 baseEnd_2350627 := by
    simpa [prefixWord, tailWord_2350627, baseEnd_2350627] using wordTrace_append hprefix tailTrace_2350627
  have hstable : (prefixWord ++ tailWord_2350627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350627).length < 2 ^ (prefixWord ++ tailWord_2350627).sum := by decide
  have hdescent : baseEnd_2350627 < baseStart_2350627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350638 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2350638 : Nat := 118140960795 + 2350638 * 2 ^ 59
def prefixEnd_2350638 : Nat := 4983230072969 + 3 ^ 40 * 2350638 * 2
def baseEnd_2350638 : Nat := 804671425815652901143079

theorem tailTrace_2350638 : CollatzResearch.WordTrace tailWord_2350638 prefixEnd_2350638 804671425815652901143079 := by
  unfold tailWord_2350638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10716851407255932231735571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57156540838698305235923045 10716851407255932231735571)
  ·
    refine ⟨16075277110883898347603357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10716851407255932231735571 16075277110883898347603357)
    ·
      refine ⟨6028228916581461880351259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16075277110883898347603357 6028228916581461880351259)
      ·
        refine ⟨9042343374872192820526889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6028228916581461880351259 9042343374872192820526889)
        ·
          refine ⟨6781757531154144615395167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9042343374872192820526889 6781757531154144615395167)
          ·
            refine ⟨10172636296731216923092751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6781757531154144615395167 10172636296731216923092751)
            ·
              refine ⟨15258954445096825384639127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10172636296731216923092751 15258954445096825384639127)
              ·
                refine ⟨22888431667645238076958691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15258954445096825384639127 22888431667645238076958691)
                ·
                  refine ⟨34332647501467857115438037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22888431667645238076958691 34332647501467857115438037)
                  ·
                    refine ⟨804671425815652901143079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34332647501467857115438037 804671425815652901143079)
                    ·
                      rfl

theorem cell22_2350638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2350638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350638 prefixEnd_2350638 := by exact prefixLift 2350638
  have htrace : WordTrace (prefixWord ++ tailWord_2350638) baseStart_2350638 baseEnd_2350638 := by
    simpa [prefixWord, tailWord_2350638, baseEnd_2350638] using wordTrace_append hprefix tailTrace_2350638
  have hstable : (prefixWord ++ tailWord_2350638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350638).length < 2 ^ (prefixWord ++ tailWord_2350638).sum := by decide
  have hdescent : baseEnd_2350638 < baseStart_2350638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350698 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_2350698 : Nat := 118140960795 + 2350698 * 2 ^ 59
def prefixEnd_2350698 : Nat := 4983230072969 + 3 ^ 40 * 2350698 * 2
def baseEnd_2350698 : Nat := 804691965041832744642895

theorem tailTrace_2350698 : CollatzResearch.WordTrace tailWord_2350698 prefixEnd_2350698 804691965041832744642895 := by
  unfold tailWord_2350698
  simp only [CollatzResearch.WordTrace]
  refine ⟨21434249909457522025267187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57157999758553392067379165 21434249909457522025267187)
  ·
    refine ⟨32151374864186283037900781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21434249909457522025267187 32151374864186283037900781)
    ·
      refine ⟨12056765574069856139212793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32151374864186283037900781 12056765574069856139212793)
      ·
        refine ⟨9042574180552392104409595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12056765574069856139212793 9042574180552392104409595)
        ·
          refine ⟨13563861270828588156614393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9042574180552392104409595 13563861270828588156614393)
          ·
            refine ⟨10172895953121441117460795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13563861270828588156614393 10172895953121441117460795)
            ·
              refine ⟨15259343929682161676191193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10172895953121441117460795 15259343929682161676191193)
              ·
                refine ⟨11444507947261621257143395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15259343929682161676191193 11444507947261621257143395)
                ·
                  refine ⟨17166761920892431885715093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11444507947261621257143395 17166761920892431885715093)
                  ·
                    refine ⟨804691965041832744642895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17166761920892431885715093 804691965041832744642895)
                    ·
                      rfl

theorem cell22_2350698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_2350698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350698 prefixEnd_2350698 := by exact prefixLift 2350698
  have htrace : WordTrace (prefixWord ++ tailWord_2350698) baseStart_2350698 baseEnd_2350698 := by
    simpa [prefixWord, tailWord_2350698, baseEnd_2350698] using wordTrace_append hprefix tailTrace_2350698
  have hstable : (prefixWord ++ tailWord_2350698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350698).length < 2 ^ (prefixWord ++ tailWord_2350698).sum := by decide
  have hdescent : baseEnd_2350698 < baseStart_2350698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350711 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 1, 9]
def baseStart_2350711 : Nat := 118140960795 + 2350711 * 2 ^ 59
def prefixEnd_2350711 : Nat := 4983230072969 + 3 ^ 40 * 2350711 * 2
def baseEnd_2350711 : Nat := 804696415207505044067855

theorem tailTrace_2350711 : CollatzResearch.WordTrace tailWord_2350711 prefixEnd_2350711 804696415207505044067855 := by
  unfold tailWord_2350711
  simp only [CollatzResearch.WordTrace]
  refine ⟨85737473786782991321291987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57158315857855327547527991 85737473786782991321291987)
  ·
    refine ⟨128606210680174486981937981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85737473786782991321291987 128606210680174486981937981)
    ·
      refine ⟨48227329005065432618226743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128606210680174486981937981 48227329005065432618226743)
      ·
        refine ⟨72340993507598148927340115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48227329005065432618226743 72340993507598148927340115)
        ·
          refine ⟨108511490261397223391010173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72340993507598148927340115 108511490261397223391010173)
          ·
            refine ⟨40691808848023958771628815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108511490261397223391010173 40691808848023958771628815)
            ·
              refine ⟨61037713272035938157443223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40691808848023958771628815 61037713272035938157443223)
              ·
                refine ⟨91556569908053907236164835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61037713272035938157443223 91556569908053907236164835)
                ·
                  refine ⟨137334854862080860854247253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91556569908053907236164835 137334854862080860854247253)
                  ·
                    refine ⟨804696415207505044067855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 137334854862080860854247253 804696415207505044067855)
                    ·
                      rfl

theorem cell22_2350711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_2350711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350711 prefixEnd_2350711 := by exact prefixLift 2350711
  have htrace : WordTrace (prefixWord ++ tailWord_2350711) baseStart_2350711 baseEnd_2350711 := by
    simpa [prefixWord, tailWord_2350711, baseEnd_2350711] using wordTrace_append hprefix tailTrace_2350711
  have hstable : (prefixWord ++ tailWord_2350711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350711).length < 2 ^ (prefixWord ++ tailWord_2350711).sum := by decide
  have hdescent : baseEnd_2350711 < baseStart_2350711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350751 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 2, 3]
def baseStart_2350751 : Nat := 118140960795 + 2350751 * 2 ^ 59
def prefixEnd_2350751 : Nat := 4983230072969 + 3 ^ 40 * 2350751 * 2
def baseEnd_2350751 : Nat := 804710108024958273067733

theorem tailTrace_2350751 : CollatzResearch.WordTrace tailWord_2350751 prefixEnd_2350751 804710108024958273067733 := by
  unfold tailWord_2350751
  simp only [CollatzResearch.WordTrace]
  refine ⟨85738932706638078152748107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57159288471092052101832071 85738932706638078152748107)
  ·
    refine ⟨128608399059957117229122161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85738932706638078152748107 128608399059957117229122161)
    ·
      refine ⟨96456299294967837921841621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128608399059957117229122161 96456299294967837921841621)
      ·
        refine ⟨2260694514725808701293163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 96456299294967837921841621 2260694514725808701293163)
        ·
          refine ⟨3391041772088713051939745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260694514725808701293163 3391041772088713051939745)
          ·
            refine ⟨2543281329066534788954809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3391041772088713051939745 2543281329066534788954809)
            ·
              refine ⟨1907460996799901091716107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2543281329066534788954809 1907460996799901091716107)
              ·
                refine ⟨2861191495199851637574161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907460996799901091716107 2861191495199851637574161)
                ·
                  refine ⟨2145893621399888728180621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2861191495199851637574161 2145893621399888728180621)
                  ·
                    refine ⟨804710108024958273067733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145893621399888728180621 804710108024958273067733)
                    ·
                      rfl

theorem cell22_2350751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 2, 3].length) (baseStart_2350751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350751 prefixEnd_2350751 := by exact prefixLift 2350751
  have htrace : WordTrace (prefixWord ++ tailWord_2350751) baseStart_2350751 baseEnd_2350751 := by
    simpa [prefixWord, tailWord_2350751, baseEnd_2350751] using wordTrace_append hprefix tailTrace_2350751
  have hstable : (prefixWord ++ tailWord_2350751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350751).length < 2 ^ (prefixWord ++ tailWord_2350751).sum := by decide
  have hdescent : baseEnd_2350751 < baseStart_2350751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350852 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_2350852 : Nat := 118140960795 + 2350852 * 2 ^ 59
def prefixEnd_2350852 : Nat := 4983230072969 + 3 ^ 40 * 2350852 * 2
def baseEnd_2350852 : Nat := 804744682389027676292423

theorem tailTrace_2350852 : CollatzResearch.WordTrace tailWord_2350852 prefixEnd_2350852 804744682389027676292423 := by
  unfold tailWord_2350852
  simp only [CollatzResearch.WordTrace]
  refine ⟨42871308239636086201087405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57161744319514781601449873 42871308239636086201087405)
  ·
    refine ⟨16076740589863532325407777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42871308239636086201087405 16076740589863532325407777)
    ·
      refine ⟨12057555442397649244055833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16076740589863532325407777 12057555442397649244055833)
      ·
        refine ⟨9043166581798236933041875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12057555442397649244055833 9043166581798236933041875)
        ·
          refine ⟨13564749872697355399562813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9043166581798236933041875 13564749872697355399562813)
          ·
            refine ⟨5086781202261508274836055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13564749872697355399562813 5086781202261508274836055)
            ·
              refine ⟨7630171803392262412254083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5086781202261508274836055 7630171803392262412254083)
              ·
                refine ⟨11445257705088393618381125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7630171803392262412254083 11445257705088393618381125)
                ·
                  refine ⟨2145985819704073803446461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11445257705088393618381125 2145985819704073803446461)
                  ·
                    refine ⟨804744682389027676292423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2145985819704073803446461 804744682389027676292423)
                    ·
                      rfl

theorem cell22_2350852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_2350852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350852 prefixEnd_2350852 := by exact prefixLift 2350852
  have htrace : WordTrace (prefixWord ++ tailWord_2350852) baseStart_2350852 baseEnd_2350852 := by
    simpa [prefixWord, tailWord_2350852, baseEnd_2350852] using wordTrace_append hprefix tailTrace_2350852
  have hstable : (prefixWord ++ tailWord_2350852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350852).length < 2 ^ (prefixWord ++ tailWord_2350852).sum := by decide
  have hdescent : baseEnd_2350852 < baseStart_2350852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350869 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 2, 3]
def baseStart_2350869 : Nat := 118140960795 + 2350869 * 2 ^ 59
def prefixEnd_2350869 : Nat := 4983230072969 + 3 ^ 40 * 2350869 * 2
def baseEnd_2350869 : Nat := 804750501836445298617371

theorem tailTrace_2350869 : CollatzResearch.WordTrace tailWord_2350869 prefixEnd_2350869 804750501836445298617371 := by
  unfold tailWord_2350869
  simp only [CollatzResearch.WordTrace]
  refine ⟨85743236520210584305543661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57162157680140389537029107 85743236520210584305543661)
  ·
    refine ⟨32153713695078969114578873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85743236520210584305543661 32153713695078969114578873)
    ·
      refine ⟨24115285271309226835934155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32153713695078969114578873 24115285271309226835934155)
      ·
        refine ⟨36172927906963840253901233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24115285271309226835934155 36172927906963840253901233)
        ·
          refine ⟨27129695930222880190425925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36172927906963840253901233 27129695930222880190425925)
          ·
            refine ⟨5086817986916790035704861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27129695930222880190425925 5086817986916790035704861)
            ·
              refine ⟨1907556745093796263389323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5086817986916790035704861 1907556745093796263389323)
              ·
                refine ⟨2861335117640694395083985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907556745093796263389323 2861335117640694395083985)
                ·
                  refine ⟨2146001338230520796312989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2861335117640694395083985 2146001338230520796312989)
                  ·
                    refine ⟨804750501836445298617371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146001338230520796312989 804750501836445298617371)
                    ·
                      rfl

theorem cell22_2350869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_2350869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350869 prefixEnd_2350869 := by exact prefixLift 2350869
  have htrace : WordTrace (prefixWord ++ tailWord_2350869) baseStart_2350869 baseEnd_2350869 := by
    simpa [prefixWord, tailWord_2350869, baseEnd_2350869] using wordTrace_append hprefix tailTrace_2350869
  have hstable : (prefixWord ++ tailWord_2350869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350869).length < 2 ^ (prefixWord ++ tailWord_2350869).sum := by decide
  have hdescent : baseEnd_2350869 < baseStart_2350869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350957 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2350957 : Nat := 118140960795 + 2350957 * 2 ^ 59
def prefixEnd_2350957 : Nat := 4983230072969 + 3 ^ 40 * 2350957 * 2
def baseEnd_2350957 : Nat := 804780626034842402417101

theorem tailTrace_2350957 : CollatzResearch.WordTrace tailWord_2350957 prefixEnd_2350957 804780626034842402417101 := by
  unfold tailWord_2350957
  simp only [CollatzResearch.WordTrace]
  refine ⟨85746446143891775334747125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57164297429261183556498083 85746446143891775334747125)
  ·
    refine ⟨8038729325989853937632543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85746446143891775334747125 8038729325989853937632543)
    ·
      refine ⟨12058093988984780906448815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8038729325989853937632543 12058093988984780906448815)
      ·
        refine ⟨18087140983477171359673223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12058093988984780906448815 18087140983477171359673223)
        ·
          refine ⟨27130711475215757039509835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18087140983477171359673223 27130711475215757039509835)
          ·
            refine ⟨40696067212823635559264753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27130711475215757039509835 40696067212823635559264753)
            ·
              refine ⟨30522050409617726669448565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40696067212823635559264753 30522050409617726669448565)
              ·
                refine ⟨2861442225901661875260803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30522050409617726669448565 2861442225901661875260803)
                ·
                  refine ⟨4292163338852492812891205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861442225901661875260803 4292163338852492812891205)
                  ·
                    refine ⟨804780626034842402417101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4292163338852492812891205 804780626034842402417101)
                    ·
                      rfl

theorem cell22_2350957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2350957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350957 prefixEnd_2350957 := by exact prefixLift 2350957
  have htrace : WordTrace (prefixWord ++ tailWord_2350957) baseStart_2350957 baseEnd_2350957 := by
    simpa [prefixWord, tailWord_2350957, baseEnd_2350957] using wordTrace_append hprefix tailTrace_2350957
  have hstable : (prefixWord ++ tailWord_2350957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350957).length < 2 ^ (prefixWord ++ tailWord_2350957).sum := by decide
  have hdescent : baseEnd_2350957 < baseStart_2350957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350974 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2350974 : Nat := 118140960795 + 2350974 * 2 ^ 59
def prefixEnd_2350974 : Nat := 4983230072969 + 3 ^ 40 * 2350974 * 2
def baseEnd_2350974 : Nat := 804786445482260024742049

theorem tailTrace_2350974 : CollatzResearch.WordTrace tailWord_2350974 prefixEnd_2350974 804786445482260024742049 := by
  unfold tailWord_2350974
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718383273103773404764497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57164710789886791492077317 10718383273103773404764497)
  ·
    refine ⟨8038787454827830053573373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10718383273103773404764497 8038787454827830053573373)
    ·
      refine ⟨3014545295560436270090015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8038787454827830053573373 3014545295560436270090015)
      ·
        refine ⟨4521817943340654405135023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014545295560436270090015 4521817943340654405135023)
        ·
          refine ⟨6782726915010981607702535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4521817943340654405135023 6782726915010981607702535)
          ·
            refine ⟨10174090372516472411553803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6782726915010981607702535 10174090372516472411553803)
            ·
              refine ⟨15261135558774708617330705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10174090372516472411553803 15261135558774708617330705)
              ·
                refine ⟨11445851669081031462998029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15261135558774708617330705 11445851669081031462998029)
                ·
                  refine ⟨4292194375905386798624261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11445851669081031462998029 4292194375905386798624261)
                  ·
                    refine ⟨804786445482260024742049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4292194375905386798624261 804786445482260024742049)
                    ·
                      rfl

theorem cell22_2350974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2350974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350974 prefixEnd_2350974 := by exact prefixLift 2350974
  have htrace : WordTrace (prefixWord ++ tailWord_2350974) baseStart_2350974 baseEnd_2350974 := by
    simpa [prefixWord, tailWord_2350974, baseEnd_2350974] using wordTrace_append hprefix tailTrace_2350974
  have hstable : (prefixWord ++ tailWord_2350974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350974).length < 2 ^ (prefixWord ++ tailWord_2350974).sum := by decide
  have hdescent : baseEnd_2350974 < baseStart_2350974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2350985 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_2350985 : Nat := 118140960795 + 2350985 * 2 ^ 59
def prefixEnd_2350985 : Nat := 4983230072969 + 3 ^ 40 * 2350985 * 2
def baseEnd_2350985 : Nat := 804790211007059662717015

theorem tailTrace_2350985 : CollatzResearch.WordTrace tailWord_2350985 prefixEnd_2350985 804790211007059662717015 := by
  unfold tailWord_2350985
  simp only [CollatzResearch.WordTrace]
  refine ⟨85747467387790336116766409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57164978258526890744510939 85747467387790336116766409)
  ·
    refine ⟨64310600540842752087574807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85747467387790336116766409 64310600540842752087574807)
    ·
      refine ⟨96465900811264128131362211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64310600540842752087574807 96465900811264128131362211)
      ·
        refine ⟨144698851216896192197043317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96465900811264128131362211 144698851216896192197043317)
        ·
          refine ⟨13565517301584018018472811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144698851216896192197043317 13565517301584018018472811)
          ·
            refine ⟨20348275952376027027709217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13565517301584018018472811 20348275952376027027709217)
            ·
              refine ⟨15261206964282020270781913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20348275952376027027709217 15261206964282020270781913)
              ·
                refine ⟨11445905223211515203086435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15261206964282020270781913 11445905223211515203086435)
                ·
                  refine ⟨17168857834817272804629653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11445905223211515203086435 17168857834817272804629653)
                  ·
                    refine ⟨804790211007059662717015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17168857834817272804629653 804790211007059662717015)
                    ·
                      rfl

theorem cell22_2350985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_2350985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2350985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2350985 prefixEnd_2350985 := by exact prefixLift 2350985
  have htrace : WordTrace (prefixWord ++ tailWord_2350985) baseStart_2350985 baseEnd_2350985 := by
    simpa [prefixWord, tailWord_2350985, baseEnd_2350985] using wordTrace_append hprefix tailTrace_2350985
  have hstable : (prefixWord ++ tailWord_2350985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2350985).length < 2 ^ (prefixWord ++ tailWord_2350985).sum := by decide
  have hdescent : baseEnd_2350985 < baseStart_2350985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2350985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351002 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_2351002 : Nat := 118140960795 + 2351002 * 2 ^ 59
def prefixEnd_2351002 : Nat := 4983230072969 + 3 ^ 40 * 2351002 * 2
def baseEnd_2351002 : Nat := 804796030454477285041963

theorem tailTrace_2351002 : CollatzResearch.WordTrace tailWord_2351002 prefixEnd_2351002 804796030454477285041963 := by
  unfold tailWord_2351002
  simp only [CollatzResearch.WordTrace]
  refine ⟨21437021857182187005033815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57165391619152498680090173 21437021857182187005033815)
  ·
    refine ⟨32155532785773280507550723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21437021857182187005033815 32155532785773280507550723)
    ·
      refine ⟨48233299178659920761326085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32155532785773280507550723 48233299178659920761326085)
      ·
        refine ⟨9043743595998735142748641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48233299178659920761326085 9043743595998735142748641)
        ·
          refine ⟨6782807696999051357061481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9043743595998735142748641 6782807696999051357061481)
          ·
            refine ⟨5087105772749288517796111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6782807696999051357061481 5087105772749288517796111)
            ·
              refine ⟨7630658659123932776694167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5087105772749288517796111 7630658659123932776694167)
              ·
                refine ⟨11445987988685899165041251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7630658659123932776694167 11445987988685899165041251)
                ·
                  refine ⟨17168981983028848747561877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11445987988685899165041251 17168981983028848747561877)
                  ·
                    refine ⟨804796030454477285041963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17168981983028848747561877 804796030454477285041963)
                    ·
                      rfl

theorem cell22_2351002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_2351002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351002 prefixEnd_2351002 := by exact prefixLift 2351002
  have htrace : WordTrace (prefixWord ++ tailWord_2351002) baseStart_2351002 baseEnd_2351002 := by
    simpa [prefixWord, tailWord_2351002, baseEnd_2351002] using wordTrace_append hprefix tailTrace_2351002
  have hstable : (prefixWord ++ tailWord_2351002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351002).length < 2 ^ (prefixWord ++ tailWord_2351002).sum := by decide
  have hdescent : baseEnd_2351002 < baseStart_2351002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351068 : List Nat := [2, 2, 6, 1, 2, 1, 8]
def baseStart_2351068 : Nat := 118140960795 + 2351068 * 2 ^ 59
def prefixEnd_2351068 : Nat := 4983230072969 + 3 ^ 40 * 2351068 * 2
def baseEnd_2351068 : Nat := 29808097170491670847843

theorem tailTrace_2351068 : CollatzResearch.WordTrace tailWord_2351068 prefixEnd_2351068 29808097170491670847843 := by
  unfold tailWord_2351068
  simp only [CollatzResearch.WordTrace]
  refine ⟨42875247323244820646018929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57166996430993094194691905 42875247323244820646018929)
  ·
    refine ⟨32156435492433615484514197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42875247323244820646018929 32156435492433615484514197)
    ·
      refine ⟨1507332913707825725836603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32156435492433615484514197 1507332913707825725836603)
      ·
        refine ⟨2260999370561738588754905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507332913707825725836603 2260999370561738588754905)
        ·
          refine ⟨1695749527921303941566179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2260999370561738588754905 1695749527921303941566179)
          ·
            refine ⟨2543624291881955912349269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695749527921303941566179 2543624291881955912349269)
            ·
              refine ⟨29808097170491670847843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2543624291881955912349269 29808097170491670847843)
              ·
                rfl

theorem cell22_2351068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 8].length) (baseStart_2351068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351068 prefixEnd_2351068 := by exact prefixLift 2351068
  have htrace : WordTrace (prefixWord ++ tailWord_2351068) baseStart_2351068 baseEnd_2351068 := by
    simpa [prefixWord, tailWord_2351068, baseEnd_2351068] using wordTrace_append hprefix tailTrace_2351068
  have hstable : (prefixWord ++ tailWord_2351068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351068).length < 2 ^ (prefixWord ++ tailWord_2351068).sum := by decide
  have hdescent : baseEnd_2351068 < baseStart_2351068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351109 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_2351109 : Nat := 118140960795 + 2351109 * 2 ^ 59
def prefixEnd_2351109 : Nat := 4983230072969 + 3 ^ 40 * 2351109 * 2
def baseEnd_2351109 : Nat := 804832658741164672616635

theorem tailTrace_2351109 : CollatzResearch.WordTrace tailWord_2351109 prefixEnd_2351109 804832658741164672616635 := by
  unfold tailWord_2351109
  simp only [CollatzResearch.WordTrace]
  refine ⟨85751990039341105294280381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57167993359560736862853587 85751990039341105294280381)
  ·
    refine ⟨32156996264752914485355143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85751990039341105294280381 32156996264752914485355143)
    ·
      refine ⟨48235494397129371728032715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32156996264752914485355143 48235494397129371728032715)
      ·
        refine ⟨72353241595694057592049073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48235494397129371728032715 72353241595694057592049073)
        ·
          refine ⟨54264931196770543194036805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72353241595694057592049073 54264931196770543194036805)
          ·
            refine ⟨10174674599394476848881901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54264931196770543194036805 10174674599394476848881901)
            ·
              refine ⟨3815502974772928818330713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10174674599394476848881901 3815502974772928818330713)
              ·
                refine ⟨2861627231079696613748035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3815502974772928818330713 2861627231079696613748035)
                ·
                  refine ⟨4292440846619544920622053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2861627231079696613748035 4292440846619544920622053)
                  ·
                    refine ⟨804832658741164672616635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4292440846619544920622053 804832658741164672616635)
                    ·
                      rfl

theorem cell22_2351109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_2351109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351109 prefixEnd_2351109 := by exact prefixLift 2351109
  have htrace : WordTrace (prefixWord ++ tailWord_2351109) baseStart_2351109 baseEnd_2351109 := by
    simpa [prefixWord, tailWord_2351109, baseEnd_2351109] using wordTrace_append hprefix tailTrace_2351109
  have hstable : (prefixWord ++ tailWord_2351109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351109).length < 2 ^ (prefixWord ++ tailWord_2351109).sum := by decide
  have hdescent : baseEnd_2351109 < baseStart_2351109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351141 : List Nat := [1, 3, 1, 2, 2, 3, 4, 2, 4]
def baseStart_2351141 : Nat := 118140960795 + 2351141 * 2 ^ 59
def prefixEnd_2351141 : Nat := 4983230072969 + 3 ^ 40 * 2351141 * 2
def baseEnd_2351141 : Nat := 268281204331709085272179

theorem tailTrace_2351141 : CollatzResearch.WordTrace tailWord_2351141 prefixEnd_2351141 268281204331709085272179 := by
  unfold tailWord_2351141
  simp only [CollatzResearch.WordTrace]
  refine ⟨85753157175225174759445277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57168771450150116506296851 85753157175225174759445277)
  ·
    refine ⟨32157433940709440534791979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85753157175225174759445277 32157433940709440534791979)
    ·
      refine ⟨48236150911064160802187969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32157433940709440534791979 48236150911064160802187969)
      ·
        refine ⟨36177113183298120601640977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48236150911064160802187969 36177113183298120601640977)
        ·
          refine ⟨27132834887473590451230733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36177113183298120601640977 27132834887473590451230733)
          ·
            refine ⟨10174813082802596419211525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27132834887473590451230733 10174813082802596419211525)
            ·
              refine ⟨1907777453025486828602161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10174813082802596419211525 1907777453025486828602161)
              ·
                refine ⟨1430833089769115121451621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1907777453025486828602161 1430833089769115121451621)
                ·
                  refine ⟨268281204331709085272179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430833089769115121451621 268281204331709085272179)
                  ·
                    rfl

theorem cell22_2351141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_2351141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351141 prefixEnd_2351141 := by exact prefixLift 2351141
  have htrace : WordTrace (prefixWord ++ tailWord_2351141) baseStart_2351141 baseEnd_2351141 := by
    simpa [prefixWord, tailWord_2351141, baseEnd_2351141] using wordTrace_append hprefix tailTrace_2351141
  have hstable : (prefixWord ++ tailWord_2351141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351141).length < 2 ^ (prefixWord ++ tailWord_2351141).sum := by decide
  have hdescent : baseEnd_2351141 < baseStart_2351141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351152 : List Nat := [2, 1, 1, 1, 2, 5, 3, 7]
def baseStart_2351152 : Nat := 118140960795 + 2351152 * 2 ^ 59
def prefixEnd_2351152 : Nat := 4983230072969 + 3 ^ 40 * 2351152 * 2
def baseEnd_2351152 : Nat := 89427486502214099310167

theorem tailTrace_2351152 : CollatzResearch.WordTrace tailWord_2351152 prefixEnd_2351152 89427486502214099310167 := by
  unfold tailWord_2351152
  simp only [CollatzResearch.WordTrace]
  refine ⟨42876779189092661819047855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57169038918790215758730473 42876779189092661819047855)
  ·
    refine ⟨64315168783638992728571783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42876779189092661819047855 64315168783638992728571783)
    ·
      refine ⟨96472753175458489092857675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64315168783638992728571783 96472753175458489092857675)
      ·
        refine ⟨144709129763187733639286513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96472753175458489092857675 144709129763187733639286513)
        ·
          refine ⟨108531847322390800229464885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144709129763187733639286513 108531847322390800229464885)
          ·
            refine ⟨10174860686474137521512333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108531847322390800229464885 10174860686474137521512333)
            ·
              refine ⟨3815572757427801570567125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10174860686474137521512333 3815572757427801570567125)
              ·
                refine ⟨89427486502214099310167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3815572757427801570567125 89427486502214099310167)
                ·
                  rfl

theorem cell22_2351152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 7].length) (baseStart_2351152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351152 prefixEnd_2351152 := by exact prefixLift 2351152
  have htrace : WordTrace (prefixWord ++ tailWord_2351152) baseStart_2351152 baseEnd_2351152 := by
    simpa [prefixWord, tailWord_2351152, baseEnd_2351152] using wordTrace_append hprefix tailTrace_2351152
  have hstable : (prefixWord ++ tailWord_2351152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351152).length < 2 ^ (prefixWord ++ tailWord_2351152).sum := by decide
  have hdescent : baseEnd_2351152 < baseStart_2351152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351190 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2351190 : Nat := 118140960795 + 2351190 * 2 ^ 59
def prefixEnd_2351190 : Nat := 4983230072969 + 3 ^ 40 * 2351190 * 2
def baseEnd_2351190 : Nat := 804860386696507461341387

theorem tailTrace_2351190 : CollatzResearch.WordTrace tailWord_2351190 prefixEnd_2351190 804860386696507461341387 := by
  unfold tailWord_2351190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5359684022002978507998689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57169962901365104085319349 5359684022002978507998689)
  ·
    refine ⟨4019763016502233880999017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5359684022002978507998689 4019763016502233880999017)
    ·
      refine ⟨3014822262376675410749263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4019763016502233880999017 3014822262376675410749263)
      ·
        refine ⟨4522233393565013116123895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014822262376675410749263 4522233393565013116123895)
        ·
          refine ⟨6783350090347519674185843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4522233393565013116123895 6783350090347519674185843)
          ·
            refine ⟨10175025135521279511278765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6783350090347519674185843 10175025135521279511278765)
            ·
              refine ⟨3815634425820479816729537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10175025135521279511278765 3815634425820479816729537)
              ·
                refine ⟨2861725819365359862547153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3815634425820479816729537 2861725819365359862547153)
                ·
                  refine ⟨2146294364524019896910365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2861725819365359862547153 2146294364524019896910365)
                  ·
                    refine ⟨804860386696507461341387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146294364524019896910365 804860386696507461341387)
                    ·
                      rfl

theorem cell22_2351190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2351190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351190 prefixEnd_2351190 := by exact prefixLift 2351190
  have htrace : WordTrace (prefixWord ++ tailWord_2351190) baseStart_2351190 baseEnd_2351190 := by
    simpa [prefixWord, tailWord_2351190, baseEnd_2351190] using wordTrace_append hprefix tailTrace_2351190
  have hstable : (prefixWord ++ tailWord_2351190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351190).length < 2 ^ (prefixWord ++ tailWord_2351190).sum := by decide
  have hdescent : baseEnd_2351190 < baseStart_2351190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351252 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2351252 : Nat := 118140960795 + 2351252 * 2 ^ 59
def prefixEnd_2351252 : Nat := 4983230072969 + 3 ^ 40 * 2351252 * 2
def baseEnd_2351252 : Nat := 804881610563559966291197

theorem tailTrace_2351252 : CollatzResearch.WordTrace tailWord_2351252 prefixEnd_2351252 804881610563559966291197 := by
  unfold tailWord_2351252
  simp only [CollatzResearch.WordTrace]
  refine ⟨42878602838911520358368005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57171470451882027144490673 42878602838911520358368005)
  ·
    refine ⟨8039738032295910067194001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42878602838911520358368005 8039738032295910067194001)
    ·
      refine ⟨6029803524221932550395501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8039738032295910067194001 6029803524221932550395501)
      ·
        refine ⟨2261176321583224706398313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6029803524221932550395501 2261176321583224706398313)
        ·
          refine ⟨1695882241187418529798735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2261176321583224706398313 1695882241187418529798735)
          ·
            refine ⟨2543823361781127794698103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695882241187418529798735 2543823361781127794698103)
            ·
              refine ⟨3815735042671691692047155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2543823361781127794698103 3815735042671691692047155)
              ·
                refine ⟨5723602564007537538070733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3815735042671691692047155 5723602564007537538070733)
                ·
                  refine ⟨2146350961502826576776525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5723602564007537538070733 2146350961502826576776525)
                  ·
                    refine ⟨804881610563559966291197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146350961502826576776525 804881610563559966291197)
                    ·
                      rfl

theorem cell22_2351252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2351252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351252 prefixEnd_2351252 := by exact prefixLift 2351252
  have htrace : WordTrace (prefixWord ++ tailWord_2351252) baseStart_2351252 baseEnd_2351252 := by
    simpa [prefixWord, tailWord_2351252, baseEnd_2351252] using wordTrace_append hprefix tailTrace_2351252
  have hstable : (prefixWord ++ tailWord_2351252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351252).length < 2 ^ (prefixWord ++ tailWord_2351252).sum := by decide
  have hdescent : baseEnd_2351252 < baseStart_2351252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351310 : List Nat := [4, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_2351310 : Nat := 118140960795 + 2351310 * 2 ^ 59
def prefixEnd_2351310 : Nat := 4983230072969 + 3 ^ 40 * 2351310 * 2
def baseEnd_2351310 : Nat := 268300488382955716113673

theorem tailTrace_2351310 : CollatzResearch.WordTrace tailWord_2351310 prefixEnd_2351310 268300488382955716113673 := by
  unfold tailWord_2351310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10719915138951614577793423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57172880741075277748231589 10719915138951614577793423)
  ·
    refine ⟨16079872708427421866690135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10719915138951614577793423 16079872708427421866690135)
    ·
      refine ⟨24119809062641132800035203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16079872708427421866690135 24119809062641132800035203)
      ·
        refine ⟨36179713593961699200052805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24119809062641132800035203 36179713593961699200052805)
        ·
          refine ⟨6783696298867818600009901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36179713593961699200052805 6783696298867818600009901)
          ·
            refine ⟨2543886112075431975003713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6783696298867818600009901 2543886112075431975003713)
            ·
              refine ⟨1907914584056573981252785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2543886112075431975003713 1907914584056573981252785)
              ·
                refine ⟨1430935938042430485939589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1907914584056573981252785 1430935938042430485939589)
                ·
                  refine ⟨268300488382955716113673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1430935938042430485939589 268300488382955716113673)
                  ·
                    rfl

theorem cell22_2351310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_2351310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351310 prefixEnd_2351310 := by exact prefixLift 2351310
  have htrace : WordTrace (prefixWord ++ tailWord_2351310) baseStart_2351310 baseEnd_2351310 := by
    simpa [prefixWord, tailWord_2351310, baseEnd_2351310] using wordTrace_append hprefix tailTrace_2351310
  have hstable : (prefixWord ++ tailWord_2351310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351310).length < 2 ^ (prefixWord ++ tailWord_2351310).sum := by decide
  have hdescent : baseEnd_2351310 < baseStart_2351310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351336 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 5, 3]
def baseStart_2351336 : Nat := 118140960795 + 2351336 * 2 ^ 59
def prefixEnd_2351336 : Nat := 4983230072969 + 3 ^ 40 * 2351336 * 2
def baseEnd_2351336 : Nat := 804910365480211747190939

theorem tailTrace_2351336 : CollatzResearch.WordTrace tailWord_2351336 prefixEnd_2351336 804910365480211747190939 := by
  unfold tailWord_2351336
  simp only [CollatzResearch.WordTrace]
  refine ⟨42880134704759361531396931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57173512939679148708529241 42880134704759361531396931)
  ·
    refine ⟨64320202057139042297095397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42880134704759361531396931 64320202057139042297095397)
    ·
      refine ⟨12060037885713570430705387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64320202057139042297095397 12060037885713570430705387)
      ·
        refine ⟨18090056828570355646058081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12060037885713570430705387 18090056828570355646058081)
        ·
          refine ⟨13567542621427766734543561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18090056828570355646058081 13567542621427766734543561)
          ·
            refine ⟨10175656966070825050907671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13567542621427766734543561 10175656966070825050907671)
            ·
              refine ⟨15263485449106237576361507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10175656966070825050907671 15263485449106237576361507)
              ·
                refine ⟨22895228173659356364542261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15263485449106237576361507 22895228173659356364542261)
                ·
                  refine ⟨2146427641280564659175837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22895228173659356364542261 2146427641280564659175837)
                  ·
                    refine ⟨804910365480211747190939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146427641280564659175837 804910365480211747190939)
                    ·
                      rfl

theorem cell22_2351336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_2351336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351336 prefixEnd_2351336 := by exact prefixLift 2351336
  have htrace : WordTrace (prefixWord ++ tailWord_2351336) baseStart_2351336 baseEnd_2351336 := by
    simpa [prefixWord, tailWord_2351336, baseEnd_2351336] using wordTrace_append hprefix tailTrace_2351336
  have hstable : (prefixWord ++ tailWord_2351336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351336).length < 2 ^ (prefixWord ++ tailWord_2351336).sum := by decide
  have hdescent : baseEnd_2351336 < baseStart_2351336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351379 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 5, 4]
def baseStart_2351379 : Nat := 118140960795 + 2351379 * 2 ^ 59
def prefixEnd_2351379 : Nat := 4983230072969 + 3 ^ 40 * 2351379 * 2
def baseEnd_2351379 : Nat := 804925085258973968365807

theorem tailTrace_2351379 : CollatzResearch.WordTrace tailWord_2351379 prefixEnd_2351379 804925085258973968365807 := by
  unfold tailWord_2351379
  simp only [CollatzResearch.WordTrace]
  refine ⟨85761837748362941406609191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57174558498908627604406127 85761837748362941406609191)
  ·
    refine ⟨128642756622544412109913787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85761837748362941406609191 128642756622544412109913787)
    ·
      refine ⟨192964134933816618164870681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128642756622544412109913787 192964134933816618164870681)
      ·
        refine ⟨144723101200362463623653011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192964134933816618164870681 144723101200362463623653011)
        ·
          refine ⟨217084651800543695435479517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144723101200362463623653011 217084651800543695435479517)
          ·
            refine ⟨81406744425203885788304819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217084651800543695435479517 81406744425203885788304819)
            ·
              refine ⟨122110116637805828682457229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81406744425203885788304819 122110116637805828682457229)
              ·
                refine ⟨45791293739177185755921461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122110116637805828682457229 45791293739177185755921461)
                ·
                  refine ⟨4292933788047861164617637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45791293739177185755921461 4292933788047861164617637)
                  ·
                    refine ⟨804925085258973968365807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4292933788047861164617637 804925085258973968365807)
                    ·
                      rfl

theorem cell22_2351379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 4].length) (baseStart_2351379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351379 prefixEnd_2351379 := by exact prefixLift 2351379
  have htrace : WordTrace (prefixWord ++ tailWord_2351379) baseStart_2351379 baseEnd_2351379 := by
    simpa [prefixWord, tailWord_2351379, baseEnd_2351379] using wordTrace_append hprefix tailTrace_2351379
  have hstable : (prefixWord ++ tailWord_2351379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351379).length < 2 ^ (prefixWord ++ tailWord_2351379).sum := by decide
  have hdescent : baseEnd_2351379 < baseStart_2351379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351383 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 5]
def baseStart_2351383 : Nat := 118140960795 + 2351383 * 2 ^ 59
def prefixEnd_2351383 : Nat := 4983230072969 + 3 ^ 40 * 2351383 * 2
def baseEnd_2351383 : Nat := 268308818180239763755265

theorem tailTrace_2351383 : CollatzResearch.WordTrace tailWord_2351383 prefixEnd_2351383 268308818180239763755265 := by
  unfold tailWord_2351383
  simp only [CollatzResearch.WordTrace]
  refine ⟨85761983640348450089754803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57174655760232300059836535 85761983640348450089754803)
  ·
    refine ⟨128642975460522675134632205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85761983640348450089754803 128642975460522675134632205)
    ·
      refine ⟨48241115797696003175487077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128642975460522675134632205 48241115797696003175487077)
      ·
        refine ⟨9045209212068000595403827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48241115797696003175487077 9045209212068000595403827)
        ·
          refine ⟨13567813818102000893105741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9045209212068000595403827 13567813818102000893105741)
          ·
            refine ⟨5087930181788250334914653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13567813818102000893105741 5087930181788250334914653)
            ·
              refine ⟨1907973818170593875592995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5087930181788250334914653 1907973818170593875592995)
              ·
                refine ⟨2861960727255890813389493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1907973818170593875592995 2861960727255890813389493)
                ·
                  refine ⟨268308818180239763755265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2861960727255890813389493 268308818180239763755265)
                  ·
                    rfl

theorem cell22_2351383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 5].length) (baseStart_2351383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351383 prefixEnd_2351383 := by exact prefixLift 2351383
  have htrace : WordTrace (prefixWord ++ tailWord_2351383) baseStart_2351383 baseEnd_2351383 := by
    simpa [prefixWord, tailWord_2351383, baseEnd_2351383] using wordTrace_append hprefix tailTrace_2351383
  have hstable : (prefixWord ++ tailWord_2351383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351383).length < 2 ^ (prefixWord ++ tailWord_2351383).sum := by decide
  have hdescent : baseEnd_2351383 < baseStart_2351383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351424 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_2351424 : Nat := 118140960795 + 2351424 * 2 ^ 59
def prefixEnd_2351424 : Nat := 4983230072969 + 3 ^ 40 * 2351424 * 2
def baseEnd_2351424 : Nat := 804940489678608850990669

theorem tailTrace_2351424 : CollatzResearch.WordTrace tailWord_2351424 prefixEnd_2351424 804940489678608850990669 := by
  unfold tailWord_2351424
  simp only [CollatzResearch.WordTrace]
  refine ⟨42881739516599957045998663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57175652688799942727998217 42881739516599957045998663)
  ·
    refine ⟨64322609274899935568997995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42881739516599957045998663 64322609274899935568997995)
    ·
      refine ⟨96483913912349903353496993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64322609274899935568997995 96483913912349903353496993)
      ·
        refine ⟨72362935434262427515122745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96483913912349903353496993 72362935434262427515122745)
        ·
          refine ⟨54272201575696820636342059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72362935434262427515122745 54272201575696820636342059)
          ·
            refine ⟨81408302363545230954513089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54272201575696820636342059 81408302363545230954513089)
            ·
              refine ⟨61056226772658923215884817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81408302363545230954513089 61056226772658923215884817)
              ·
                refine ⟨45792170079494192411913613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61056226772658923215884817 45792170079494192411913613)
                ·
                  refine ⟨17172063779810322154467605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45792170079494192411913613 17172063779810322154467605)
                  ·
                    refine ⟨804940489678608850990669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17172063779810322154467605 804940489678608850990669)
                    ·
                      rfl

theorem cell22_2351424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_2351424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351424 prefixEnd_2351424 := by exact prefixLift 2351424
  have htrace : WordTrace (prefixWord ++ tailWord_2351424) baseStart_2351424 baseEnd_2351424 := by
    simpa [prefixWord, tailWord_2351424, baseEnd_2351424] using wordTrace_append hprefix tailTrace_2351424
  have hstable : (prefixWord ++ tailWord_2351424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351424).length < 2 ^ (prefixWord ++ tailWord_2351424).sum := by decide
  have hdescent : baseEnd_2351424 < baseStart_2351424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351458 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2351458 : Nat := 118140960795 + 2351458 * 2 ^ 59
def prefixEnd_2351458 : Nat := 4983230072969 + 3 ^ 40 * 2351458 * 2
def baseEnd_2351458 : Nat := 804952128573444095640565

theorem tailTrace_2351458 : CollatzResearch.WordTrace tailWord_2351458 prefixEnd_2351458 804952128573444095640565 := by
  unfold tailWord_2351458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21441179778769184474683757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57176479410051158599156685 21441179778769184474683757)
  ·
    refine ⟨8040442417038444178006409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21441179778769184474683757 8040442417038444178006409)
    ·
      refine ⟨6030331812778833133504807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8040442417038444178006409 6030331812778833133504807)
      ·
        refine ⟨9045497719168249700257211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6030331812778833133504807 9045497719168249700257211)
        ·
          refine ⟨13568246578752374550385817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9045497719168249700257211 13568246578752374550385817)
          ·
            refine ⟨10176184934064280912789363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13568246578752374550385817 10176184934064280912789363)
            ·
              refine ⟨15264277401096421369184045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10176184934064280912789363 15264277401096421369184045)
              ·
                refine ⟨5724104025411158013444017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15264277401096421369184045 5724104025411158013444017)
                ·
                  refine ⟨4293078019058368510083013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5724104025411158013444017 4293078019058368510083013)
                  ·
                    refine ⟨804952128573444095640565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293078019058368510083013 804952128573444095640565)
                    ·
                      rfl

theorem cell22_2351458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2351458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351458 prefixEnd_2351458 := by exact prefixLift 2351458
  have htrace : WordTrace (prefixWord ++ tailWord_2351458) baseStart_2351458 baseEnd_2351458 := by
    simpa [prefixWord, tailWord_2351458, baseEnd_2351458] using wordTrace_append hprefix tailTrace_2351458
  have hstable : (prefixWord ++ tailWord_2351458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351458).length < 2 ^ (prefixWord ++ tailWord_2351458).sum := by decide
  have hdescent : baseEnd_2351458 < baseStart_2351458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351471 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 7, 3]
def baseStart_2351471 : Nat := 118140960795 + 2351471 * 2 ^ 59
def prefixEnd_2351471 : Nat := 4983230072969 + 3 ^ 40 * 2351471 * 2
def baseEnd_2351471 : Nat := 804956578739116395065525

theorem tailTrace_2351471 : CollatzResearch.WordTrace tailWord_2351471 prefixEnd_2351471 804956578739116395065525 := by
  unfold tailWord_2351471
  simp only [CollatzResearch.WordTrace]
  refine ⟨85765193264029641118958267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57176795509353094079305511 85765193264029641118958267)
  ·
    refine ⟨128647789896044461678437401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85765193264029641118958267 128647789896044461678437401)
    ·
      refine ⟨96485842422033346258828051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128647789896044461678437401 96485842422033346258828051)
      ·
        refine ⟨144728763633050019388242077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96485842422033346258828051 144728763633050019388242077)
        ·
          refine ⟨54273286362393757270590779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144728763633050019388242077 54273286362393757270590779)
          ·
            refine ⟨81409929543590635905886169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54273286362393757270590779 81409929543590635905886169)
            ·
              refine ⟨61057447157692976929414627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81409929543590635905886169 61057447157692976929414627)
              ·
                refine ⟨91586170736539465394121941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61057447157692976929414627 91586170736539465394121941)
                ·
                  refine ⟨2146550876637643720174733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 91586170736539465394121941 2146550876637643720174733)
                  ·
                    refine ⟨804956578739116395065525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146550876637643720174733 804956578739116395065525)
                    ·
                      rfl

theorem cell22_2351471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_2351471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351471 prefixEnd_2351471 := by exact prefixLift 2351471
  have htrace : WordTrace (prefixWord ++ tailWord_2351471) baseStart_2351471 baseEnd_2351471 := by
    simpa [prefixWord, tailWord_2351471, baseEnd_2351471] using wordTrace_append hprefix tailTrace_2351471
  have hstable : (prefixWord ++ tailWord_2351471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351471).length < 2 ^ (prefixWord ++ tailWord_2351471).sum := by decide
  have hdescent : baseEnd_2351471 < baseStart_2351471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351522 : List Nat := [3, 3, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2351522 : Nat := 118140960795 + 2351522 * 2 ^ 59
def prefixEnd_2351522 : Nat := 4983230072969 + 3 ^ 40 * 2351522 * 2
def baseEnd_2351522 : Nat := 804974037081369262040369

theorem tailTrace_2351522 : CollatzResearch.WordTrace tailWord_2351522 prefixEnd_2351522 804974037081369262040369 := by
  unfold tailWord_2351522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21441763346711219207266205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57178035591229917886043213 21441763346711219207266205)
  ·
    refine ⟨8040661255016707202724827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21441763346711219207266205 8040661255016707202724827)
    ·
      refine ⟨12060991882525060804087241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8040661255016707202724827 12060991882525060804087241)
      ·
        refine ⟨9045743911893795603065431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12060991882525060804087241 9045743911893795603065431)
        ·
          refine ⟨13568615867840693404598147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9045743911893795603065431 13568615867840693404598147)
          ·
            refine ⟨20352923801761040106897221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13568615867840693404598147 20352923801761040106897221)
            ·
              refine ⟨3816173212830195020043229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20352923801761040106897221 3816173212830195020043229)
              ·
                refine ⟨1431064954811323132516211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3816173212830195020043229 1431064954811323132516211)
                ·
                  refine ⟨2146597432216984698774317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431064954811323132516211 2146597432216984698774317)
                  ·
                    refine ⟨804974037081369262040369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146597432216984698774317 804974037081369262040369)
                    ·
                      rfl

theorem cell22_2351522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2351522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351522 prefixEnd_2351522 := by exact prefixLift 2351522
  have htrace : WordTrace (prefixWord ++ tailWord_2351522) baseStart_2351522 baseEnd_2351522 := by
    simpa [prefixWord, tailWord_2351522, baseEnd_2351522] using wordTrace_append hprefix tailTrace_2351522
  have hstable : (prefixWord ++ tailWord_2351522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351522).length < 2 ^ (prefixWord ++ tailWord_2351522).sum := by decide
  have hdescent : baseEnd_2351522 < baseStart_2351522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351578 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 6, 3]
def baseStart_2351578 : Nat := 118140960795 + 2351578 * 2 ^ 59
def prefixEnd_2351578 : Nat := 4983230072969 + 3 ^ 40 * 2351578 * 2
def baseEnd_2351578 : Nat := 804993207025803782640197

theorem tailTrace_2351578 : CollatzResearch.WordTrace tailWord_2351578 prefixEnd_2351578 804993207025803782640197 := by
  unfold tailWord_2351578
  simp only [CollatzResearch.WordTrace]
  refine ⟨21442273968660499598275847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57179397249761332262068925 21442273968660499598275847)
  ·
    refine ⟨32163410952990749397413771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21442273968660499598275847 32163410952990749397413771)
    ·
      refine ⟨48245116429486124096120657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32163410952990749397413771 48245116429486124096120657)
      ·
        refine ⟨36183837322114593072090493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48245116429486124096120657 36183837322114593072090493)
        ·
          refine ⟨13568938995792972402033935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36183837322114593072090493 13568938995792972402033935)
          ·
            refine ⟨20353408493689458603050903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13568938995792972402033935 20353408493689458603050903)
            ·
              refine ⟨30530112740534187904576355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20353408493689458603050903 30530112740534187904576355)
              ·
                refine ⟨45795169110801281856864533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30530112740534187904576355 45795169110801281856864533)
                ·
                  refine ⟨2146648552068810087040525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45795169110801281856864533 2146648552068810087040525)
                  ·
                    refine ⟨804993207025803782640197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146648552068810087040525 804993207025803782640197)
                    ·
                      rfl

theorem cell22_2351578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_2351578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351578 prefixEnd_2351578 := by exact prefixLift 2351578
  have htrace : WordTrace (prefixWord ++ tailWord_2351578) baseStart_2351578 baseEnd_2351578 := by
    simpa [prefixWord, tailWord_2351578, baseEnd_2351578] using wordTrace_append hprefix tailTrace_2351578
  have hstable : (prefixWord ++ tailWord_2351578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351578).length < 2 ^ (prefixWord ++ tailWord_2351578).sum := by decide
  have hdescent : baseEnd_2351578 < baseStart_2351578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351653 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 5]
def baseStart_2351653 : Nat := 118140960795 + 2351653 * 2 ^ 59
def prefixEnd_2351653 : Nat := 4983230072969 + 3 ^ 40 * 2351653 * 2
def baseEnd_2351653 : Nat := 268339627019509529004989

theorem tailTrace_2351653 : CollatzResearch.WordTrace tailWord_2351653 prefixEnd_2351653 268339627019509529004989 := by
  unfold tailWord_2351653
  simp only [CollatzResearch.WordTrace]
  refine ⟨85771831349370286202083613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57181220899580190801389075 85771831349370286202083613)
  ·
    refine ⟨32164436756013857325781355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85771831349370286202083613 32164436756013857325781355)
    ·
      refine ⟨48246655134020785988672033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32164436756013857325781355 48246655134020785988672033)
      ·
        refine ⟨36184991350515589491504025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48246655134020785988672033 36184991350515589491504025)
        ·
          refine ⟨27138743512886692118628019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36184991350515589491504025 27138743512886692118628019)
          ·
            refine ⟨40708115269330038177942029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27138743512886692118628019 40708115269330038177942029)
            ·
              refine ⟨15265543225998764316728261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40708115269330038177942029 15265543225998764316728261)
              ·
                refine ⟨2862289354874768309386549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15265543225998764316728261 2862289354874768309386549)
                ·
                  refine ⟨268339627019509529004989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2862289354874768309386549 268339627019509529004989)
                  ·
                    rfl

theorem cell22_2351653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_2351653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351653 prefixEnd_2351653 := by exact prefixLift 2351653
  have htrace : WordTrace (prefixWord ++ tailWord_2351653) baseStart_2351653 baseEnd_2351653 := by
    simpa [prefixWord, tailWord_2351653, baseEnd_2351653] using wordTrace_append hprefix tailTrace_2351653
  have hstable : (prefixWord ++ tailWord_2351653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351653).length < 2 ^ (prefixWord ++ tailWord_2351653).sum := by decide
  have hdescent : baseEnd_2351653 < baseStart_2351653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351698 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_2351698 : Nat := 118140960795 + 2351698 * 2 ^ 59
def prefixEnd_2351698 : Nat := 4983230072969 + 3 ^ 40 * 2351698 * 2
def baseEnd_2351698 : Nat := 268344761826054489879943

theorem tailTrace_2351698 : CollatzResearch.WordTrace tailWord_2351698 prefixEnd_2351698 268344761826054489879943 := by
  unfold tailWord_2351698
  simp only [CollatzResearch.WordTrace]
  refine ⟨21443368158551814721867937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57182315089471505924981165 21443368158551814721867937)
  ·
    refine ⟨16082526118913861041400953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21443368158551814721867937 16082526118913861041400953)
    ·
      refine ⟨12061894589185395781050715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16082526118913861041400953 12061894589185395781050715)
      ·
        refine ⟨18092841883778093671576073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12061894589185395781050715 18092841883778093671576073)
        ·
          refine ⟨13569631412833570253682055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18092841883778093671576073 13569631412833570253682055)
          ·
            refine ⟨20354447119250355380523083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13569631412833570253682055 20354447119250355380523083)
            ·
              refine ⟨30531670678875533070784625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20354447119250355380523083 30531670678875533070784625)
              ·
                refine ⟨22898753009156649803088469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30531670678875533070784625 22898753009156649803088469)
                ·
                  refine ⟨268344761826054489879943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22898753009156649803088469 268344761826054489879943)
                  ·
                    rfl

theorem cell22_2351698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_2351698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351698 prefixEnd_2351698 := by exact prefixLift 2351698
  have htrace : WordTrace (prefixWord ++ tailWord_2351698) baseStart_2351698 baseEnd_2351698 := by
    simpa [prefixWord, tailWord_2351698, baseEnd_2351698] using wordTrace_append hprefix tailTrace_2351698
  have hstable : (prefixWord ++ tailWord_2351698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351698).length < 2 ^ (prefixWord ++ tailWord_2351698).sum := by decide
  have hdescent : baseEnd_2351698 < baseStart_2351698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351715 : List Nat := [1, 1, 1, 5, 1, 2, 1, 6, 4]
def baseStart_2351715 : Nat := 118140960795 + 2351715 * 2 ^ 59
def prefixEnd_2351715 : Nat := 4983230072969 + 3 ^ 40 * 2351715 * 2
def baseEnd_2351715 : Nat := 268346701641860363988259

theorem tailTrace_2351715 : CollatzResearch.WordTrace tailWord_2351715 prefixEnd_2351715 268346701641860363988259 := by
  unfold tailWord_2351715
  simp only [CollatzResearch.WordTrace]
  refine ⟨85774092675145670790840599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57182728450097113860560399 85774092675145670790840599)
  ·
    refine ⟨128661139012718506186260899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85774092675145670790840599 128661139012718506186260899)
    ·
      refine ⟨192991708519077759279391349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128661139012718506186260899 192991708519077759279391349)
      ·
        refine ⟨18092972673663539932442939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192991708519077759279391349 18092972673663539932442939)
        ·
          refine ⟨27139459010495309898664409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18092972673663539932442939 27139459010495309898664409)
          ·
            refine ⟨20354594257871482423998307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27139459010495309898664409 20354594257871482423998307)
            ·
              refine ⟨30531891386807223635997461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20354594257871482423998307 30531891386807223635997461)
              ·
                refine ⟨1431182408756588607937381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30531891386807223635997461 1431182408756588607937381)
                ·
                  refine ⟨268346701641860363988259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1431182408756588607937381 268346701641860363988259)
                  ·
                    rfl

theorem cell22_2351715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 4].length) (baseStart_2351715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351715 prefixEnd_2351715 := by exact prefixLift 2351715
  have htrace : WordTrace (prefixWord ++ tailWord_2351715) baseStart_2351715 baseEnd_2351715 := by
    simpa [prefixWord, tailWord_2351715, baseEnd_2351715] using wordTrace_append hprefix tailTrace_2351715
  have hstable : (prefixWord ++ tailWord_2351715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351715).length < 2 ^ (prefixWord ++ tailWord_2351715).sum := by decide
  have hdescent : baseEnd_2351715 < baseStart_2351715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351734 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_2351734 : Nat := 118140960795 + 2351734 * 2 ^ 59
def prefixEnd_2351734 : Nat := 4983230072969 + 3 ^ 40 * 2351734 * 2
def baseEnd_2351734 : Nat := 805046609013871375739719

theorem tailTrace_2351734 : CollatzResearch.WordTrace tailWord_2351734 prefixEnd_2351734 805046609013871375739719 := by
  unfold tailWord_2351734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5360924103879802314736391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57183190441384558023854837 5360924103879802314736391)
  ·
    refine ⟨8041386155819703472104587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5360924103879802314736391 8041386155819703472104587)
    ·
      refine ⟨12062079233729555208156881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8041386155819703472104587 12062079233729555208156881)
      ·
        refine ⟨9046559425297166406117661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12062079233729555208156881 9046559425297166406117661)
        ·
          refine ⟨3392459784486437402294123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9046559425297166406117661 3392459784486437402294123)
          ·
            refine ⟨5088689676729656103441185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3392459784486437402294123 5088689676729656103441185)
            ·
              refine ⟨3816517257547242077580889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5088689676729656103441185 3816517257547242077580889)
              ·
                refine ⟨2862387943160431558185667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816517257547242077580889 2862387943160431558185667)
                ·
                  refine ⟨4293581914740647337278501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862387943160431558185667 4293581914740647337278501)
                  ·
                    refine ⟨805046609013871375739719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293581914740647337278501 805046609013871375739719)
                    ·
                      rfl

theorem cell22_2351734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_2351734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351734 prefixEnd_2351734 := by exact prefixLift 2351734
  have htrace : WordTrace (prefixWord ++ tailWord_2351734) baseStart_2351734 baseEnd_2351734 := by
    simpa [prefixWord, tailWord_2351734, baseEnd_2351734] using wordTrace_append hprefix tailTrace_2351734
  have hstable : (prefixWord ++ tailWord_2351734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351734).length < 2 ^ (prefixWord ++ tailWord_2351734).sum := by decide
  have hdescent : baseEnd_2351734 < baseStart_2351734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351745 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2351745 : Nat := 118140960795 + 2351745 * 2 ^ 59
def prefixEnd_2351745 : Nat := 4983230072969 + 3 ^ 40 * 2351745 * 2
def baseEnd_2351745 : Nat := 805050374538671013714685

theorem tailTrace_2351745 : CollatzResearch.WordTrace tailWord_2351745 prefixEnd_2351745 805050374538671013714685 := by
  unfold tailWord_2351745
  simp only [CollatzResearch.WordTrace]
  refine ⟨85775186865036985914432689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57183457910024657276288459 85775186865036985914432689)
  ·
    refine ⟨64331390148777739435824517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85775186865036985914432689 64331390148777739435824517)
    ·
      refine ⟨12062135652895826144217097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64331390148777739435824517 12062135652895826144217097)
      ·
        refine ⟨9046601739671869608162823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12062135652895826144217097 9046601739671869608162823)
        ·
          refine ⟨13569902609507804412244235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9046601739671869608162823 13569902609507804412244235)
          ·
            refine ⟨20354853914261706618366353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13569902609507804412244235 20354853914261706618366353)
            ·
              refine ⟨15266140435696279963774765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20354853914261706618366353 15266140435696279963774765)
              ·
                refine ⟨5724802663386104986415537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15266140435696279963774765 5724802663386104986415537)
                ·
                  refine ⟨4293601997539578739811653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5724802663386104986415537 4293601997539578739811653)
                  ·
                    refine ⟨805050374538671013714685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293601997539578739811653 805050374538671013714685)
                    ·
                      rfl

theorem cell22_2351745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2351745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351745 prefixEnd_2351745 := by exact prefixLift 2351745
  have htrace : WordTrace (prefixWord ++ tailWord_2351745) baseStart_2351745 baseEnd_2351745 := by
    simpa [prefixWord, tailWord_2351745, baseEnd_2351745] using wordTrace_append hprefix tailTrace_2351745
  have hstable : (prefixWord ++ tailWord_2351745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351745).length < 2 ^ (prefixWord ++ tailWord_2351745).sum := by decide
  have hdescent : baseEnd_2351745 < baseStart_2351745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351762 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2351762 : Nat := 118140960795 + 2351762 * 2 ^ 59
def prefixEnd_2351762 : Nat := 4983230072969 + 3 ^ 40 * 2351762 * 2
def baseEnd_2351762 : Nat := 805056193986088636039633

theorem tailTrace_2351762 : CollatzResearch.WordTrace tailWord_2351762 prefixEnd_2351762 805056193986088636039633 := by
  unfold tailWord_2351762
  simp only [CollatzResearch.WordTrace]
  refine ⟨21443951726493849454450385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57183871270650265211867693 21443951726493849454450385)
  ·
    refine ⟨16082963794870387090837789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21443951726493849454450385 16082963794870387090837789)
    ·
      refine ⟨6031111423076395159064171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16082963794870387090837789 6031111423076395159064171)
      ·
        refine ⟨9046667134614592738596257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6031111423076395159064171 9046667134614592738596257)
        ·
          refine ⟨6785000350960944553947193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9046667134614592738596257 6785000350960944553947193)
          ·
            refine ⟨5088750263220708415460395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6785000350960944553947193 5088750263220708415460395)
            ·
              refine ⟨7633125394831062623190593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5088750263220708415460395 7633125394831062623190593)
              ·
                refine ⟨5724844046123296967392945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7633125394831062623190593 5724844046123296967392945)
                ·
                  refine ⟨4293633034592472725544709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5724844046123296967392945 4293633034592472725544709)
                  ·
                    refine ⟨805056193986088636039633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4293633034592472725544709 805056193986088636039633)
                    ·
                      rfl

theorem cell22_2351762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2351762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351762 prefixEnd_2351762 := by exact prefixLift 2351762
  have htrace : WordTrace (prefixWord ++ tailWord_2351762) baseStart_2351762 baseEnd_2351762 := by
    simpa [prefixWord, tailWord_2351762, baseEnd_2351762] using wordTrace_append hprefix tailTrace_2351762
  have hstable : (prefixWord ++ tailWord_2351762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351762).length < 2 ^ (prefixWord ++ tailWord_2351762).sum := by decide
  have hdescent : baseEnd_2351762 < baseStart_2351762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351803 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 6, 5]
def baseStart_2351803 : Nat := 118140960795 + 2351803 * 2 ^ 59
def prefixEnd_2351803 : Nat := 4983230072969 + 3 ^ 40 * 2351803 * 2
def baseEnd_2351803 : Nat := 805070229123978195764507

theorem tailTrace_2351803 : CollatzResearch.WordTrace tailWord_2351803 prefixEnd_2351803 805070229123978195764507 := by
  unfold tailWord_2351803
  simp only [CollatzResearch.WordTrace]
  refine ⟨85777302298826861820044063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57184868199217907880029375 85777302298826861820044063)
  ·
    refine ⟨128665953448240292730066095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85777302298826861820044063 128665953448240292730066095)
    ·
      refine ⟨192998930172360439095099143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128665953448240292730066095 192998930172360439095099143)
      ·
        refine ⟨289498395258540658642648715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192998930172360439095099143 289498395258540658642648715)
        ·
          refine ⟨434247592887810987963973073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289498395258540658642648715 434247592887810987963973073)
          ·
            refine ⟨325685694665858240972979805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434247592887810987963973073 325685694665858240972979805)
            ·
              refine ⟨122132135499696840364867427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 325685694665858240972979805 122132135499696840364867427)
              ·
                refine ⟨183198203249545260547301141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122132135499696840364867427 183198203249545260547301141)
                ·
                  refine ⟨8587415777322434088154741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 183198203249545260547301141 8587415777322434088154741)
                  ·
                    refine ⟨805070229123978195764507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8587415777322434088154741 805070229123978195764507)
                    ·
                      rfl

theorem cell22_2351803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_2351803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351803 prefixEnd_2351803 := by exact prefixLift 2351803
  have htrace : WordTrace (prefixWord ++ tailWord_2351803) baseStart_2351803 baseEnd_2351803 := by
    simpa [prefixWord, tailWord_2351803, baseEnd_2351803] using wordTrace_append hprefix tailTrace_2351803
  have hstable : (prefixWord ++ tailWord_2351803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351803).length < 2 ^ (prefixWord ++ tailWord_2351803).sum := by decide
  have hdescent : baseEnd_2351803 < baseStart_2351803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351822 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_2351822 : Nat := 118140960795 + 2351822 * 2 ^ 59
def prefixEnd_2351822 : Nat := 4983230072969 + 3 ^ 40 * 2351822 * 2
def baseEnd_2351822 : Nat := 268358911070756159846483

theorem tailTrace_2351822 : CollatzResearch.WordTrace tailWord_2351822 prefixEnd_2351822 268358911070756159846483 := by
  unfold tailWord_2351822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10722249410719753508123215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57185330190505352043323813 10722249410719753508123215)
  ·
    refine ⟨16083374116079630262184823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10722249410719753508123215 16083374116079630262184823)
    ·
      refine ⟨24125061174119445393277235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16083374116079630262184823 24125061174119445393277235)
      ·
        refine ⟨36187591761179168089915853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24125061174119445393277235 36187591761179168089915853)
        ·
          refine ⟨13570346910442188033718445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36187591761179168089915853 13570346910442188033718445)
          ·
            refine ⟨5088880091415820512644417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13570346910442188033718445 5088880091415820512644417)
            ·
              refine ⟨3816660068561865384483313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5088880091415820512644417 3816660068561865384483313)
              ·
                refine ⟨2862495051421399038362485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3816660068561865384483313 2862495051421399038362485)
                ·
                  refine ⟨268358911070756159846483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2862495051421399038362485 268358911070756159846483)
                  ·
                    rfl

theorem cell22_2351822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_2351822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351822 prefixEnd_2351822 := by exact prefixLift 2351822
  have htrace : WordTrace (prefixWord ++ tailWord_2351822) baseStart_2351822 baseEnd_2351822 := by
    simpa [prefixWord, tailWord_2351822, baseEnd_2351822] using wordTrace_append hprefix tailTrace_2351822
  have hstable : (prefixWord ++ tailWord_2351822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351822).length < 2 ^ (prefixWord ++ tailWord_2351822).sum := by decide
  have hdescent : baseEnd_2351822 < baseStart_2351822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351826 : List Nat := [3, 2, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_2351826 : Nat := 118140960795 + 2351826 * 2 ^ 59
def prefixEnd_2351826 : Nat := 4983230072969 + 3 ^ 40 * 2351826 * 2
def baseEnd_2351826 : Nat := 805078102494013802439437

theorem tailTrace_2351826 : CollatzResearch.WordTrace tailWord_2351826 prefixEnd_2351826 805078102494013802439437 := by
  unfold tailWord_2351826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21444535294435884187032833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57185427451829024498754221 21444535294435884187032833)
  ·
    refine ⟨16083401470826913140274625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21444535294435884187032833 16083401470826913140274625)
    ·
      refine ⟨12062551103120184855205969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16083401470826913140274625 12062551103120184855205969)
      ·
        refine ⟨9046913327340138641404477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12062551103120184855205969 9046913327340138641404477)
        ·
          refine ⟨3392592497752551990526679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9046913327340138641404477 3392592497752551990526679)
          ·
            refine ⟨5088888746628827985790019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3392592497752551990526679 5088888746628827985790019)
            ·
              refine ⟨7633333119943241978685029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5088888746628827985790019 7633333119943241978685029)
              ·
                refine ⟨1431249959989357871003443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7633333119943241978685029 1431249959989357871003443)
                ·
                  refine ⟨2146874939984036806505165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431249959989357871003443 2146874939984036806505165)
                  ·
                    refine ⟨805078102494013802439437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146874939984036806505165 805078102494013802439437)
                    ·
                      rfl

theorem cell22_2351826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_2351826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351826 prefixEnd_2351826 := by exact prefixLift 2351826
  have htrace : WordTrace (prefixWord ++ tailWord_2351826) baseStart_2351826 baseEnd_2351826 := by
    simpa [prefixWord, tailWord_2351826, baseEnd_2351826] using wordTrace_append hprefix tailTrace_2351826
  have hstable : (prefixWord ++ tailWord_2351826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351826).length < 2 ^ (prefixWord ++ tailWord_2351826).sum := by decide
  have hdescent : baseEnd_2351826 < baseStart_2351826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351860 : List Nat := [2, 6, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_2351860 : Nat := 118140960795 + 2351860 * 2 ^ 59
def prefixEnd_2351860 : Nat := 4983230072969 + 3 ^ 40 * 2351860 * 2
def baseEnd_2351860 : Nat := 805089741388849047089333

theorem tailTrace_2351860 : CollatzResearch.WordTrace tailWord_2351860 prefixEnd_2351860 805089741388849047089333 := by
  unfold tailWord_2351860
  simp only [CollatzResearch.WordTrace]
  refine ⟨42889690629810180277434517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57186254173080240369912689 42889690629810180277434517)
  ·
    refine ⟨2010454248272352200504743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42889690629810180277434517 2010454248272352200504743)
    ·
      refine ⟨3015681372408528300757115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2010454248272352200504743 3015681372408528300757115)
      ·
        refine ⟨4523522058612792451135673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3015681372408528300757115 4523522058612792451135673)
        ·
          refine ⟨3392641543959594338351755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4523522058612792451135673 3392641543959594338351755)
          ·
            refine ⟨5088962315939391507527633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3392641543959594338351755 5088962315939391507527633)
            ·
              refine ⟨3816721736954543630645725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5088962315939391507527633 3816721736954543630645725)
              ·
                refine ⟨1431270651357953861492147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3816721736954543630645725 1431270651357953861492147)
                ·
                  refine ⟨2146905977036930792238221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431270651357953861492147 2146905977036930792238221)
                  ·
                    refine ⟨805089741388849047089333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146905977036930792238221 805089741388849047089333)
                    ·
                      rfl

theorem cell22_2351860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_2351860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351860 prefixEnd_2351860 := by exact prefixLift 2351860
  have htrace : WordTrace (prefixWord ++ tailWord_2351860) baseStart_2351860 baseEnd_2351860 := by
    simpa [prefixWord, tailWord_2351860, baseEnd_2351860] using wordTrace_append hprefix tailTrace_2351860
  have hstable : (prefixWord ++ tailWord_2351860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351860).length < 2 ^ (prefixWord ++ tailWord_2351860).sum := by decide
  have hdescent : baseEnd_2351860 < baseStart_2351860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351882 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_2351882 : Nat := 118140960795 + 2351882 * 2 ^ 59
def prefixEnd_2351882 : Nat := 4983230072969 + 3 ^ 40 * 2351882 * 2
def baseEnd_2351882 : Nat := 805097272438448323039265

theorem tailTrace_2351882 : CollatzResearch.WordTrace tailWord_2351882 prefixEnd_2351882 805097272438448323039265 := by
  unfold tailWord_2351882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21445045916385164578042475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57186789110360438874779933 21445045916385164578042475)
  ·
    refine ⟨32167568874577746867063713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21445045916385164578042475 32167568874577746867063713)
    ·
      refine ⟨24125676655933310150297785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32167568874577746867063713 24125676655933310150297785)
      ·
        refine ⟨18094257491949982612723339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24125676655933310150297785 18094257491949982612723339)
        ·
          refine ⟨27141386237924973919085009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18094257491949982612723339 27141386237924973919085009)
          ·
            refine ⟨20356039678443730439313757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27141386237924973919085009 20356039678443730439313757)
            ·
              refine ⟨7633514879416398914742659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20356039678443730439313757 7633514879416398914742659)
              ·
                refine ⟨11450272319124598372113989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7633514879416398914742659 11450272319124598372113989)
                ·
                  refine ⟨2146926059835862194771373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11450272319124598372113989 2146926059835862194771373)
                  ·
                    refine ⟨805097272438448323039265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2146926059835862194771373 805097272438448323039265)
                    ·
                      rfl

theorem cell22_2351882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_2351882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351882 prefixEnd_2351882 := by exact prefixLift 2351882
  have htrace : WordTrace (prefixWord ++ tailWord_2351882) baseStart_2351882 baseEnd_2351882 := by
    simpa [prefixWord, tailWord_2351882, baseEnd_2351882] using wordTrace_append hprefix tailTrace_2351882
  have hstable : (prefixWord ++ tailWord_2351882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351882).length < 2 ^ (prefixWord ++ tailWord_2351882).sum := by decide
  have hdescent : baseEnd_2351882 < baseStart_2351882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351955 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 2, 5]
def baseStart_2351955 : Nat := 118140960795 + 2351955 * 2 ^ 59
def prefixEnd_2351955 : Nat := 4983230072969 + 3 ^ 40 * 2351955 * 2
def baseEnd_2351955 : Nat := 805122261830300465964041

theorem tailTrace_2351955 : CollatzResearch.WordTrace tailWord_2351955 prefixEnd_2351955 805122261830300465964041 := by
  unfold tailWord_2351955
  simp only [CollatzResearch.WordTrace]
  refine ⟨85782846194276191779577319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57188564129517461186384879 85782846194276191779577319)
  ·
    refine ⟨128674269291414287669365979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85782846194276191779577319 128674269291414287669365979)
    ·
      refine ⟨193011403937121431504048969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128674269291414287669365979 193011403937121431504048969)
      ·
        refine ⟨144758552952841073628036727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193011403937121431504048969 144758552952841073628036727)
        ·
          refine ⟨217137829429261610442055091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144758552952841073628036727 217137829429261610442055091)
          ·
            refine ⟨325706744143892415663082637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217137829429261610442055091 325706744143892415663082637)
            ·
              refine ⟨122140029053959655873655989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 325706744143892415663082637 122140029053959655873655989)
              ·
                refine ⟨11450627723808717738155249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122140029053959655873655989 11450627723808717738155249)
                ·
                  refine ⟨8587970792856538303616437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11450627723808717738155249 8587970792856538303616437)
                  ·
                    refine ⟨805122261830300465964041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8587970792856538303616437 805122261830300465964041)
                    ·
                      rfl

theorem cell22_2351955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_2351955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351955 prefixEnd_2351955 := by exact prefixLift 2351955
  have htrace : WordTrace (prefixWord ++ tailWord_2351955) baseStart_2351955 baseEnd_2351955 := by
    simpa [prefixWord, tailWord_2351955, baseEnd_2351955] using wordTrace_append hprefix tailTrace_2351955
  have hstable : (prefixWord ++ tailWord_2351955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351955).length < 2 ^ (prefixWord ++ tailWord_2351955).sum := by decide
  have hdescent : baseEnd_2351955 < baseStart_2351955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351957 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 5]
def baseStart_2351957 : Nat := 118140960795 + 2351957 * 2 ^ 59
def prefixEnd_2351957 : Nat := 4983230072969 + 3 ^ 40 * 2351957 * 2
def baseEnd_2351957 : Nat := 268374315490391042471345

theorem tailTrace_2351957 : CollatzResearch.WordTrace tailWord_2351957 prefixEnd_2351957 268374315490391042471345 := by
  unfold tailWord_2351957
  simp only [CollatzResearch.WordTrace]
  refine ⟨85782919140268946121150125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57188612760179297414100083 85782919140268946121150125)
  ·
    refine ⟨32168594677600854795431297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85782919140268946121150125 32168594677600854795431297)
    ·
      refine ⟨24126446008200641096573473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32168594677600854795431297 24126446008200641096573473)
      ·
        refine ⟨18094834506150480822430105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24126446008200641096573473 18094834506150480822430105)
        ·
          refine ⟨13571125879612860616822579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18094834506150480822430105 13571125879612860616822579)
          ·
            refine ⟨20356688819419290925233869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13571125879612860616822579 20356688819419290925233869)
            ·
              refine ⟨7633758307282234096962701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20356688819419290925233869 7633758307282234096962701)
              ·
                refine ⟨2862659365230837786361013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7633758307282234096962701 2862659365230837786361013)
                ·
                  refine ⟨268374315490391042471345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2862659365230837786361013 268374315490391042471345)
                  ·
                    rfl

theorem cell22_2351957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_2351957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351957 prefixEnd_2351957 := by exact prefixLift 2351957
  have htrace : WordTrace (prefixWord ++ tailWord_2351957) baseStart_2351957 baseEnd_2351957 := by
    simpa [prefixWord, tailWord_2351957, baseEnd_2351957] using wordTrace_append hprefix tailTrace_2351957
  have hstable : (prefixWord ++ tailWord_2351957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351957).length < 2 ^ (prefixWord ++ tailWord_2351957).sum := by decide
  have hdescent : baseEnd_2351957 < baseStart_2351957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2351987 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 1, 4]
def baseStart_2351987 : Nat := 118140960795 + 2351987 * 2 ^ 59
def prefixEnd_2351987 : Nat := 4983230072969 + 3 ^ 40 * 2351987 * 2
def baseEnd_2351987 : Nat := 805133216084263049163943

theorem tailTrace_2351987 : CollatzResearch.WordTrace tailWord_2351987 prefixEnd_2351987 805133216084263049163943 := by
  unfold tailWord_2351987
  simp only [CollatzResearch.WordTrace]
  refine ⟨85784013330160261244742215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57189342220106840829828143 85784013330160261244742215)
  ·
    refine ⟨128676019995240391867113323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85784013330160261244742215 128676019995240391867113323)
    ·
      refine ⟨193014029992860587800669985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128676019995240391867113323 193014029992860587800669985)
      ·
        refine ⟨144760522494645440850502489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193014029992860587800669985 144760522494645440850502489)
        ·
          refine ⟨108570391870984080637876867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144760522494645440850502489 108570391870984080637876867)
          ·
            refine ⟨162855587806476120956815301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108570391870984080637876867 162855587806476120956815301)
            ·
              refine ⟨30535422713714272679402869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 162855587806476120956815301 30535422713714272679402869)
              ·
                refine ⟨2862695879410713063694019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30535422713714272679402869 2862695879410713063694019)
                ·
                  refine ⟨4294043819116069595541029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2862695879410713063694019 4294043819116069595541029)
                  ·
                    refine ⟨805133216084263049163943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294043819116069595541029 805133216084263049163943)
                    ·
                      rfl

theorem cell22_2351987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 4].length) (baseStart_2351987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2351987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2351987 prefixEnd_2351987 := by exact prefixLift 2351987
  have htrace : WordTrace (prefixWord ++ tailWord_2351987) baseStart_2351987 baseEnd_2351987 := by
    simpa [prefixWord, tailWord_2351987, baseEnd_2351987] using wordTrace_append hprefix tailTrace_2351987
  have hstable : (prefixWord ++ tailWord_2351987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2351987).length < 2 ^ (prefixWord ++ tailWord_2351987).sum := by decide
  have hdescent : baseEnd_2351987 < baseStart_2351987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2351987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352017 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 6, 3]
def baseStart_2352017 : Nat := 118140960795 + 2352017 * 2 ^ 59
def prefixEnd_2352017 : Nat := 4983230072969 + 3 ^ 40 * 2352017 * 2
def baseEnd_2352017 : Nat := 805143485697352970913851

theorem tailTrace_2352017 : CollatzResearch.WordTrace tailWord_2352017 prefixEnd_2352017 805143485697352970913851 := by
  unfold tailWord_2352017
  simp only [CollatzResearch.WordTrace]
  refine ⟨85785107520051576368334305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57190071680034384245556203 85785107520051576368334305)
  ·
    refine ⟨64338830640038682276250729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85785107520051576368334305 64338830640038682276250729)
    ·
      refine ⟨48254122980029011707188047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64338830640038682276250729 48254122980029011707188047)
      ·
        refine ⟨72381184470043517560782071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48254122980029011707188047 72381184470043517560782071)
        ·
          refine ⟨108571776705065276341173107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72381184470043517560782071 108571776705065276341173107)
          ·
            refine ⟨162857665057597914511759661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108571776705065276341173107 162857665057597914511759661)
            ·
              refine ⟨61071624396599217941909873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162857665057597914511759661 61071624396599217941909873)
              ·
                refine ⟨45803718297449413456432405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61071624396599217941909873 45803718297449413456432405)
                ·
                  refine ⟨2147049295192941255770269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45803718297449413456432405 2147049295192941255770269)
                  ·
                    refine ⟨805143485697352970913851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147049295192941255770269 805143485697352970913851)
                    ·
                      rfl

theorem cell22_2352017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_2352017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352017 prefixEnd_2352017 := by exact prefixLift 2352017
  have htrace : WordTrace (prefixWord ++ tailWord_2352017) baseStart_2352017 baseEnd_2352017 := by
    simpa [prefixWord, tailWord_2352017, baseEnd_2352017] using wordTrace_append hprefix tailTrace_2352017
  have hstable : (prefixWord ++ tailWord_2352017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352017).length < 2 ^ (prefixWord ++ tailWord_2352017).sum := by decide
  have hdescent : baseEnd_2352017 < baseStart_2352017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352034 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2352034 : Nat := 118140960795 + 2352034 * 2 ^ 59
def prefixEnd_2352034 : Nat := 4983230072969 + 3 ^ 40 * 2352034 * 2
def baseEnd_2352034 : Nat := 805149305144770593238799

theorem tailTrace_2352034 : CollatzResearch.WordTrace tailWord_2352034 prefixEnd_2352034 805149305144770593238799 := by
  unfold tailWord_2352034
  simp only [CollatzResearch.WordTrace]
  refine ⟨21446431890247497067925789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57190485040659992181135437 21446431890247497067925789)
  ·
    refine ⟨8042411958842811400472171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21446431890247497067925789 8042411958842811400472171)
    ·
      refine ⟨12063617938264217100708257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8042411958842811400472171 12063617938264217100708257)
      ·
        refine ⟨9047713453698162825531193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12063617938264217100708257 9047713453698162825531193)
        ·
          refine ⟨6785785090273622119148395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9047713453698162825531193 6785785090273622119148395)
          ·
            refine ⟨10178677635410433178722593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6785785090273622119148395 10178677635410433178722593)
            ·
              refine ⟨7634008226557824884041945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10178677635410433178722593 7634008226557824884041945)
              ·
                refine ⟨5725506169918368663031459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7634008226557824884041945 5725506169918368663031459)
                ·
                  refine ⟨8588259254877552994547189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5725506169918368663031459 8588259254877552994547189)
                  ·
                    refine ⟨805149305144770593238799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8588259254877552994547189 805149305144770593238799)
                    ·
                      rfl

theorem cell22_2352034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2352034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352034 prefixEnd_2352034 := by exact prefixLift 2352034
  have htrace : WordTrace (prefixWord ++ tailWord_2352034) baseStart_2352034 baseEnd_2352034 := by
    simpa [prefixWord, tailWord_2352034, baseEnd_2352034] using wordTrace_append hprefix tailTrace_2352034
  have hstable : (prefixWord ++ tailWord_2352034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352034).length < 2 ^ (prefixWord ++ tailWord_2352034).sum := by decide
  have hdescent : baseEnd_2352034 < baseStart_2352034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352068 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2352068 : Nat := 118140960795 + 2352068 * 2 ^ 59
def prefixEnd_2352068 : Nat := 4983230072969 + 3 ^ 40 * 2352068 * 2
def baseEnd_2352068 : Nat := 805160944039605837888695

theorem tailTrace_2352068 : CollatzResearch.WordTrace tailWord_2352068 prefixEnd_2352068 805160944039605837888695 := by
  unfold tailWord_2352068
  simp only [CollatzResearch.WordTrace]
  refine ⟨42893483821433406039220429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57191311761911208052293905 42893483821433406039220429)
  ·
    refine ⟨16085056433037527264707661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42893483821433406039220429 16085056433037527264707661)
    ·
      refine ⟨6031896162389072724265373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16085056433037527264707661 6031896162389072724265373)
      ·
        refine ⟨2261961060895902271599515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6031896162389072724265373 2261961060895902271599515)
        ·
          refine ⟨3392941591343853407399273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2261961060895902271599515 3392941591343853407399273)
          ·
            refine ⟨2544706193507890055549455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3392941591343853407399273 2544706193507890055549455)
            ·
              refine ⟨3817059290261835083324183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544706193507890055549455 3817059290261835083324183)
              ·
                refine ⟨5725588935392752624986275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817059290261835083324183 5725588935392752624986275)
                ·
                  refine ⟨8588383403089128937479413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5725588935392752624986275 8588383403089128937479413)
                  ·
                    refine ⟨805160944039605837888695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8588383403089128937479413 805160944039605837888695)
                    ·
                      rfl

theorem cell22_2352068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2352068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352068 prefixEnd_2352068 := by exact prefixLift 2352068
  have htrace : WordTrace (prefixWord ++ tailWord_2352068) baseStart_2352068 baseEnd_2352068 := by
    simpa [prefixWord, tailWord_2352068, baseEnd_2352068] using wordTrace_append hprefix tailTrace_2352068
  have hstable : (prefixWord ++ tailWord_2352068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352068).length < 2 ^ (prefixWord ++ tailWord_2352068).sum := by decide
  have hdescent : baseEnd_2352068 < baseStart_2352068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352079 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 3, 3]
def baseStart_2352079 : Nat := 118140960795 + 2352079 * 2 ^ 59
def prefixEnd_2352079 : Nat := 4983230072969 + 3 ^ 40 * 2352079 * 2
def baseEnd_2352079 : Nat := 805164709564405475863661

theorem tailTrace_2352079 : CollatzResearch.WordTrace tailWord_2352079 prefixEnd_2352079 805164709564405475863661 := by
  unfold tailWord_2352079
  simp only [CollatzResearch.WordTrace]
  refine ⟨85787368845826960957091291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57191579230551307304727527 85787368845826960957091291)
  ·
    refine ⟨128681053268740441435636937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85787368845826960957091291 128681053268740441435636937)
    ·
      refine ⟨96510789951555331076727703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128681053268740441435636937 96510789951555331076727703)
      ·
        refine ⟨144766184927332996615091555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96510789951555331076727703 144766184927332996615091555)
        ·
          refine ⟨217149277390999494922637333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144766184927332996615091555 217149277390999494922637333)
          ·
            refine ⟨10178872377703101324498625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 217149277390999494922637333 10178872377703101324498625)
            ·
              refine ⟨7634154283277325993373969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10178872377703101324498625 7634154283277325993373969)
              ·
                refine ⟨5725615712457994495030477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7634154283277325993373969 5725615712457994495030477)
                ·
                  refine ⟨2147105892171747935636429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5725615712457994495030477 2147105892171747935636429)
                  ·
                    refine ⟨805164709564405475863661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147105892171747935636429 805164709564405475863661)
                    ·
                      rfl

theorem cell22_2352079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_2352079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352079 prefixEnd_2352079 := by exact prefixLift 2352079
  have htrace : WordTrace (prefixWord ++ tailWord_2352079) baseStart_2352079 baseEnd_2352079 := by
    simpa [prefixWord, tailWord_2352079, baseEnd_2352079] using wordTrace_append hprefix tailTrace_2352079
  have hstable : (prefixWord ++ tailWord_2352079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352079).length < 2 ^ (prefixWord ++ tailWord_2352079).sum := by decide
  have hdescent : baseEnd_2352079 < baseStart_2352079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352137 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 6]
def baseStart_2352137 : Nat := 118140960795 + 2352137 * 2 ^ 59
def prefixEnd_2352137 : Nat := 4983230072969 + 3 ^ 40 * 2352137 * 2
def baseEnd_2352137 : Nat := 268394854716570885971161

theorem tailTrace_2352137 : CollatzResearch.WordTrace tailWord_2352137 prefixEnd_2352137 268394854716570885971161 := by
  unfold tailWord_2352137
  simp only [CollatzResearch.WordTrace]
  refine ⟨85789484279616836862702665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57192989519744557908468443 85789484279616836862702665)
  ·
    refine ⟨64342113209712627647026999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85789484279616836862702665 64342113209712627647026999)
    ·
      refine ⟨96513169814568941470540499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64342113209712627647026999 96513169814568941470540499)
      ·
        refine ⟨144769754721853412205810749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96513169814568941470540499 144769754721853412205810749)
        ·
          refine ⟨54288658020695029577179031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144769754721853412205810749 54288658020695029577179031)
          ·
            refine ⟨81432987031042544365768547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54288658020695029577179031 81432987031042544365768547)
            ·
              refine ⟨122149480546563816548652821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81432987031042544365768547 122149480546563816548652821)
              ·
                refine ⟨5725756900620178900718101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122149480546563816548652821 5725756900620178900718101)
                ·
                  refine ⟨268394854716570885971161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5725756900620178900718101 268394854716570885971161)
                  ·
                    rfl

theorem cell22_2352137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_2352137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352137 prefixEnd_2352137 := by exact prefixLift 2352137
  have htrace : WordTrace (prefixWord ++ tailWord_2352137) baseStart_2352137 baseEnd_2352137 := by
    simpa [prefixWord, tailWord_2352137, baseEnd_2352137] using wordTrace_append hprefix tailTrace_2352137
  have hstable : (prefixWord ++ tailWord_2352137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352137).length < 2 ^ (prefixWord ++ tailWord_2352137).sum := by decide
  have hdescent : baseEnd_2352137 < baseStart_2352137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352139 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 3, 4]
def baseStart_2352139 : Nat := 118140960795 + 2352139 * 2 ^ 59
def prefixEnd_2352139 : Nat := 4983230072969 + 3 ^ 40 * 2352139 * 2
def baseEnd_2352139 : Nat := 805185248790585319363477

theorem tailTrace_2352139 : CollatzResearch.WordTrace tailWord_2352139 prefixEnd_2352139 805185248790585319363477 := by
  unfold tailWord_2352139
  simp only [CollatzResearch.WordTrace]
  refine ⟨85789557225609591204275471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57193038150406394136183647 85789557225609591204275471)
  ·
    refine ⟨128684335838414386806413207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85789557225609591204275471 128684335838414386806413207)
    ·
      refine ⟨193026503757621580209619811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128684335838414386806413207 193026503757621580209619811)
      ·
        refine ⟨289539755636432370314429717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193026503757621580209619811 289539755636432370314429717)
        ·
          refine ⟨13572176045457767358488893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 289539755636432370314429717 13572176045457767358488893)
          ·
            refine ⟨5089566017046662759433335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13572176045457767358488893 5089566017046662759433335)
            ·
              refine ⟨7634349025569994139150003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5089566017046662759433335 7634349025569994139150003)
              ·
                refine ⟨11451523538354991208725005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7634349025569994139150003 11451523538354991208725005)
                ·
                  refine ⟨4294321326883121703271877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11451523538354991208725005 4294321326883121703271877)
                  ·
                    refine ⟨805185248790585319363477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294321326883121703271877 805185248790585319363477)
                    ·
                      rfl

theorem cell22_2352139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 4].length) (baseStart_2352139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352139 prefixEnd_2352139 := by exact prefixLift 2352139
  have htrace : WordTrace (prefixWord ++ tailWord_2352139) baseStart_2352139 baseEnd_2352139 := by
    simpa [prefixWord, tailWord_2352139, baseEnd_2352139] using wordTrace_append hprefix tailTrace_2352139
  have hstable : (prefixWord ++ tailWord_2352139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352139).length < 2 ^ (prefixWord ++ tailWord_2352139).sum := by decide
  have hdescent : baseEnd_2352139 < baseStart_2352139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352186 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_2352186 : Nat := 118140960795 + 2352186 * 2 ^ 59
def prefixEnd_2352186 : Nat := 4983230072969 + 3 ^ 40 * 2352186 * 2
def baseEnd_2352186 : Nat := 805201337851092863438333

theorem tailTrace_2352186 : CollatzResearch.WordTrace tailWord_2352186 prefixEnd_2352186 805201337851092863438333 := by
  unfold tailWord_2352186
  simp only [CollatzResearch.WordTrace]
  refine ⟨21447817864109829557809103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57194180970959545487490941 21447817864109829557809103)
  ·
    refine ⟨32171726796164744336713655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21447817864109829557809103 32171726796164744336713655)
    ·
      refine ⟨48257590194247116505070483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32171726796164744336713655 48257590194247116505070483)
      ·
        refine ⟨72386385291370674757605725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48257590194247116505070483 72386385291370674757605725)
        ·
          refine ⟨27144894484264003034102147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72386385291370674757605725 27144894484264003034102147)
          ·
            refine ⟨40717341726396004551153221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27144894484264003034102147 40717341726396004551153221)
            ·
              refine ⟨7634501573699250853341229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40717341726396004551153221 7634501573699250853341229)
              ·
                refine ⟨2862938090137219070002961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7634501573699250853341229 2862938090137219070002961)
                ·
                  refine ⟨2147203567602914302502221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2862938090137219070002961 2147203567602914302502221)
                  ·
                    refine ⟨805201337851092863438333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147203567602914302502221 805201337851092863438333)
                    ·
                      rfl

theorem cell22_2352186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_2352186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352186 prefixEnd_2352186 := by exact prefixLift 2352186
  have htrace : WordTrace (prefixWord ++ tailWord_2352186) baseStart_2352186 baseEnd_2352186 := by
    simpa [prefixWord, tailWord_2352186, baseEnd_2352186] using wordTrace_append hprefix tailTrace_2352186
  have hstable : (prefixWord ++ tailWord_2352186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352186).length < 2 ^ (prefixWord ++ tailWord_2352186).sum := by decide
  have hdescent : baseEnd_2352186 < baseStart_2352186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352231 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 3, 3]
def baseStart_2352231 : Nat := 118140960795 + 2352231 * 2 ^ 59
def prefixEnd_2352231 : Nat := 4983230072969 + 3 ^ 40 * 2352231 * 2
def baseEnd_2352231 : Nat := 805216742270727746063195

theorem tailTrace_2352231 : CollatzResearch.WordTrace tailWord_2352231 prefixEnd_2352231 805216742270727746063195 := by
  unfold tailWord_2352231
  simp only [CollatzResearch.WordTrace]
  refine ⟨85792912741276290916624547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57195275160850860611083031 85792912741276290916624547)
  ·
    refine ⟨128689369111914436374936821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85792912741276290916624547 128689369111914436374936821)
    ·
      refine ⟨12064628354241978410150327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128689369111914436374936821 12064628354241978410150327)
      ·
        refine ⟨18096942531362967615225491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12064628354241978410150327 18096942531362967615225491)
        ·
          refine ⟨27145413797044451422838237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18096942531362967615225491 27145413797044451422838237)
          ·
            refine ⟨10179530173891669283564339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27145413797044451422838237 10179530173891669283564339)
            ·
              refine ⟨15269295260837503925346509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10179530173891669283564339 15269295260837503925346509)
              ·
                refine ⟨5725985722814063972004941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15269295260837503925346509 5725985722814063972004941)
                ·
                  refine ⟨2147244646055273989501853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5725985722814063972004941 2147244646055273989501853)
                  ·
                    refine ⟨805216742270727746063195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147244646055273989501853 805216742270727746063195)
                    ·
                      rfl

theorem cell22_2352231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_2352231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352231 prefixEnd_2352231 := by exact prefixLift 2352231
  have htrace : WordTrace (prefixWord ++ tailWord_2352231) baseStart_2352231 baseEnd_2352231 := by
    simpa [prefixWord, tailWord_2352231, baseEnd_2352231] using wordTrace_append hprefix tailTrace_2352231
  have hstable : (prefixWord ++ tailWord_2352231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352231).length < 2 ^ (prefixWord ++ tailWord_2352231).sum := by decide
  have hdescent : baseEnd_2352231 < baseStart_2352231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352265 : List Nat := [1, 2, 1, 1, 4, 5, 1, 3, 1, 3]
def baseStart_2352265 : Nat := 118140960795 + 2352265 * 2 ^ 59
def prefixEnd_2352265 : Nat := 4983230072969 + 3 ^ 40 * 2352265 * 2
def baseEnd_2352265 : Nat := 805228381165562990713091

theorem tailTrace_2352265 : CollatzResearch.WordTrace tailWord_2352265 prefixEnd_2352265 805228381165562990713091 := by
  unfold tailWord_2352265
  simp only [CollatzResearch.WordTrace]
  refine ⟨85794152823153114723362249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57196101882102076482241499 85794152823153114723362249)
  ·
    refine ⟨64345614617364836042521687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85794152823153114723362249 64345614617364836042521687)
    ·
      refine ⟨96518421926047254063782531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64345614617364836042521687 96518421926047254063782531)
      ·
        refine ⟨144777632889070881095673797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96518421926047254063782531 144777632889070881095673797)
        ·
          refine ⟨27145806166700790205438837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144777632889070881095673797 27145806166700790205438837)
          ·
            refine ⟨2544919328128199081759891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27145806166700790205438837 2544919328128199081759891)
            ·
              refine ⟨3817378992192298622639837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2544919328128199081759891 3817378992192298622639837)
              ·
                refine ⟨1431517122072111983489939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3817378992192298622639837 1431517122072111983489939)
                ·
                  refine ⟨2147275683108167975234909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431517122072111983489939 2147275683108167975234909)
                  ·
                    refine ⟨805228381165562990713091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147275683108167975234909 805228381165562990713091)
                    ·
                      rfl

theorem cell22_2352265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 1, 3].length) (baseStart_2352265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352265 prefixEnd_2352265 := by exact prefixLift 2352265
  have htrace : WordTrace (prefixWord ++ tailWord_2352265) baseStart_2352265 baseEnd_2352265 := by
    simpa [prefixWord, tailWord_2352265, baseEnd_2352265] using wordTrace_append hprefix tailTrace_2352265
  have hstable : (prefixWord ++ tailWord_2352265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352265).length < 2 ^ (prefixWord ++ tailWord_2352265).sum := by decide
  have hdescent : baseEnd_2352265 < baseStart_2352265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352282 : List Nat := [3, 1, 1, 5, 1, 2, 3, 2, 1, 3]
def baseStart_2352282 : Nat := 118140960795 + 2352282 * 2 ^ 59
def prefixEnd_2352282 : Nat := 4983230072969 + 3 ^ 40 * 2352282 * 2
def baseEnd_2352282 : Nat := 805234200612980613038039

theorem tailTrace_2352282 : CollatzResearch.WordTrace tailWord_2352282 prefixEnd_2352282 805234200612980613038039 := by
  unfold tailWord_2352282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21448693216022881656682775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57196515242727684417820733 21448693216022881656682775)
  ·
    refine ⟨32173039824034322485024163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21448693216022881656682775 32173039824034322485024163)
    ·
      refine ⟨48259559736051483727536245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32173039824034322485024163 48259559736051483727536245)
      ·
        refine ⟨4524333725254826599456523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48259559736051483727536245 4524333725254826599456523)
        ·
          refine ⟨6786500587882239899184785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524333725254826599456523 6786500587882239899184785)
          ·
            refine ⟨5089875440911679924388589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6786500587882239899184785 5089875440911679924388589)
            ·
              refine ⟨1908703290341879971645721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5089875440911679924388589 1908703290341879971645721)
              ·
                refine ⟨1431527467756409978734291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1908703290341879971645721 1431527467756409978734291)
                ·
                  refine ⟨2147291201634614968101437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431527467756409978734291 2147291201634614968101437)
                  ·
                    refine ⟨805234200612980613038039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147291201634614968101437 805234200612980613038039)
                    ·
                      rfl

theorem cell22_2352282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_2352282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352282 prefixEnd_2352282 := by exact prefixLift 2352282
  have htrace : WordTrace (prefixWord ++ tailWord_2352282) baseStart_2352282 baseEnd_2352282 := by
    simpa [prefixWord, tailWord_2352282, baseEnd_2352282] using wordTrace_append hprefix tailTrace_2352282
  have hstable : (prefixWord ++ tailWord_2352282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352282).length < 2 ^ (prefixWord ++ tailWord_2352282).sum := by decide
  have hdescent : baseEnd_2352282 < baseStart_2352282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352295 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 5]
def baseStart_2352295 : Nat := 118140960795 + 2352295 * 2 ^ 59
def prefixEnd_2352295 : Nat := 4983230072969 + 3 ^ 40 * 2352295 * 2
def baseEnd_2352295 : Nat := 268412883592884304154333

theorem tailTrace_2352295 : CollatzResearch.WordTrace tailWord_2352295 prefixEnd_2352295 268412883592884304154333 := by
  unfold tailWord_2352295
  simp only [CollatzResearch.WordTrace]
  refine ⟨85795247013044429846954339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57196831342029619897969559 85795247013044429846954339)
  ·
    refine ⟨128692870519566644770431509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85795247013044429846954339 128692870519566644770431509)
    ·
      refine ⟨6032478305604686473613977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128692870519566644770431509 6032478305604686473613977)
      ·
        refine ⟨4524358729203514855210483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6032478305604686473613977 4524358729203514855210483)
        ·
          refine ⟨6786538093805272282815725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524358729203514855210483 6786538093805272282815725)
          ·
            refine ⟨2544951785176977106055897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6786538093805272282815725 2544951785176977106055897)
            ·
              refine ⟨1908713838882732829541923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2544951785176977106055897 1908713838882732829541923)
              ·
                refine ⟨2863070758324099244312885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908713838882732829541923 2863070758324099244312885)
                ·
                  refine ⟨268412883592884304154333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2863070758324099244312885 268412883592884304154333)
                  ·
                    rfl

theorem cell22_2352295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 5].length) (baseStart_2352295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352295 prefixEnd_2352295 := by exact prefixLift 2352295
  have htrace : WordTrace (prefixWord ++ tailWord_2352295) baseStart_2352295 baseEnd_2352295 := by
    simpa [prefixWord, tailWord_2352295, baseEnd_2352295] using wordTrace_append hprefix tailTrace_2352295
  have hstable : (prefixWord ++ tailWord_2352295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352295).length < 2 ^ (prefixWord ++ tailWord_2352295).sum := by decide
  have hdescent : baseEnd_2352295 < baseStart_2352295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352319 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 1, 6]
def baseStart_2352319 : Nat := 118140960795 + 2352319 * 2 ^ 59
def prefixEnd_2352319 : Nat := 4983230072969 + 3 ^ 40 * 2352319 * 2
def baseEnd_2352319 : Nat := 805246866469124849862925

theorem tailTrace_2352319 : CollatzResearch.WordTrace tailWord_2352319 prefixEnd_2352319 805246866469124849862925 := by
  unfold tailWord_2352319
  simp only [CollatzResearch.WordTrace]
  refine ⟨85796122364957481945828011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57197414909971654630552007 85796122364957481945828011)
  ·
    refine ⟨128694183547436222918742017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85796122364957481945828011 128694183547436222918742017)
    ·
      refine ⟨96520637660577167189056513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128694183547436222918742017 96520637660577167189056513)
      ·
        refine ⟨72390478245432875391792385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96520637660577167189056513 72390478245432875391792385)
        ·
          refine ⟨54292858684074656543844289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72390478245432875391792385 54292858684074656543844289)
          ·
            refine ⟨40719644013055992407883217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54292858684074656543844289 40719644013055992407883217)
            ·
              refine ⟨30539733009791994305912413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40719644013055992407883217 30539733009791994305912413)
              ·
                refine ⟨11452399878671997864717155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30539733009791994305912413 11452399878671997864717155)
                ·
                  refine ⟨17178599818007996797075733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11452399878671997864717155 17178599818007996797075733)
                  ·
                    refine ⟨805246866469124849862925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17178599818007996797075733 805246866469124849862925)
                    ·
                      rfl

theorem cell22_2352319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_2352319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352319 prefixEnd_2352319 := by exact prefixLift 2352319
  have htrace : WordTrace (prefixWord ++ tailWord_2352319) baseStart_2352319 baseEnd_2352319 := by
    simpa [prefixWord, tailWord_2352319, baseEnd_2352319] using wordTrace_append hprefix tailTrace_2352319
  have hstable : (prefixWord ++ tailWord_2352319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352319).length < 2 ^ (prefixWord ++ tailWord_2352319).sum := by decide
  have hdescent : baseEnd_2352319 < baseStart_2352319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352333 : List Nat := [1, 6, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2352333 : Nat := 118140960795 + 2352333 * 2 ^ 59
def prefixEnd_2352333 : Nat := 4983230072969 + 3 ^ 40 * 2352333 * 2
def baseEnd_2352333 : Nat := 805251658955233480012883

theorem tailTrace_2352333 : CollatzResearch.WordTrace tailWord_2352333 prefixEnd_2352333 805251658955233480012883 := by
  unfold tailWord_2352333
  simp only [CollatzResearch.WordTrace]
  refine ⟨85796632986906762336837653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57197755324604508224558435 85796632986906762336837653)
  ·
    refine ⟨4021717171261254484539265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85796632986906762336837653 4021717171261254484539265)
    ·
      refine ⟨3016287878445940863404449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4021717171261254484539265 3016287878445940863404449)
      ·
        refine ⟨2262215908834455647553337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3016287878445940863404449 2262215908834455647553337)
        ·
          refine ⟨1696661931625841735665003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2262215908834455647553337 1696661931625841735665003)
          ·
            refine ⟨2544992897438762603497505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696661931625841735665003 2544992897438762603497505)
            ·
              refine ⟨1908744673079071952623129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2544992897438762603497505 1908744673079071952623129)
              ·
                refine ⟨1431558504809303964467347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1908744673079071952623129 1431558504809303964467347)
                ·
                  refine ⟨2147337757213955946701021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431558504809303964467347 2147337757213955946701021)
                  ·
                    refine ⟨805251658955233480012883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147337757213955946701021 805251658955233480012883)
                    ·
                      rfl

theorem cell22_2352333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2352333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352333 prefixEnd_2352333 := by exact prefixLift 2352333
  have htrace : WordTrace (prefixWord ++ tailWord_2352333) baseStart_2352333 baseEnd_2352333 := by
    simpa [prefixWord, tailWord_2352333, baseEnd_2352333] using wordTrace_append hprefix tailTrace_2352333
  have hstable : (prefixWord ++ tailWord_2352333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352333).length < 2 ^ (prefixWord ++ tailWord_2352333).sum := by decide
  have hdescent : baseEnd_2352333 < baseStart_2352333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352334 : List Nat := [4, 1, 1, 1, 15]
def baseStart_2352334 : Nat := 118140960795 + 2352334 * 2 ^ 59
def prefixEnd_2352334 : Nat := 4983230072969 + 3 ^ 40 * 2352334 * 2
def baseEnd_2352334 : Nat := 3313794243932797575053

theorem tailTrace_2352334 : CollatzResearch.WordTrace tailWord_2352334 prefixEnd_2352334 3313794243932797575053 := by
  unfold tailWord_2352334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10724583682487892438453007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57197779639935426338416037 10724583682487892438453007)
  ·
    refine ⟨16086875523731838657679511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10724583682487892438453007 16086875523731838657679511)
    ·
      refine ⟨24130313285597757986519267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16086875523731838657679511 24130313285597757986519267)
      ·
        refine ⟨36195469928396636979778901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24130313285597757986519267 36195469928396636979778901)
        ·
          refine ⟨3313794243932797575053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 36195469928396636979778901 3313794243932797575053)
          ·
            rfl

theorem cell22_2352334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 15].length) (baseStart_2352334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352334 prefixEnd_2352334 := by exact prefixLift 2352334
  have htrace : WordTrace (prefixWord ++ tailWord_2352334) baseStart_2352334 baseEnd_2352334 := by
    simpa [prefixWord, tailWord_2352334, baseEnd_2352334] using wordTrace_append hprefix tailTrace_2352334
  have hstable : (prefixWord ++ tailWord_2352334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352334).length < 2 ^ (prefixWord ++ tailWord_2352334).sum := by decide
  have hdescent : baseEnd_2352334 < baseStart_2352334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352370 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_2352370 : Nat := 118140960795 + 2352370 * 2 ^ 59
def prefixEnd_2352370 : Nat := 4983230072969 + 3 ^ 40 * 2352370 * 2
def baseEnd_2352370 : Nat := 805264324811377716837769

theorem tailTrace_2352370 : CollatzResearch.WordTrace tailWord_2352370 prefixEnd_2352370 805264324811377716837769 := by
  unfold tailWord_2352370
  simp only [CollatzResearch.WordTrace]
  refine ⟨21449495621943179413983641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57198654991848478437289709 21449495621943179413983641)
  ·
    refine ⟨16087121716457384560487731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21449495621943179413983641 16087121716457384560487731)
    ·
      refine ⟨24130682574686076840731597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16087121716457384560487731 24130682574686076840731597)
      ·
        refine ⟨9049005965507278815274349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24130682574686076840731597 9049005965507278815274349)
        ·
          refine ⟨3393377237065229555727881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9049005965507278815274349 3393377237065229555727881)
          ·
            refine ⟨2545032927798922166795911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3393377237065229555727881 2545032927798922166795911)
            ·
              refine ⟨3817549391698383250193867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545032927798922166795911 3817549391698383250193867)
              ·
                refine ⟨5726324087547574875290801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3817549391698383250193867 5726324087547574875290801)
                ·
                  refine ⟨4294743065660681156468101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5726324087547574875290801 4294743065660681156468101)
                  ·
                    refine ⟨805264324811377716837769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294743065660681156468101 805264324811377716837769)
                    ·
                      rfl

theorem cell22_2352370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_2352370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352370 prefixEnd_2352370 := by exact prefixLift 2352370
  have htrace : WordTrace (prefixWord ++ tailWord_2352370) baseStart_2352370 baseEnd_2352370 := by
    simpa [prefixWord, tailWord_2352370, baseEnd_2352370] using wordTrace_append hprefix tailTrace_2352370
  have hstable : (prefixWord ++ tailWord_2352370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352370).length < 2 ^ (prefixWord ++ tailWord_2352370).sum := by decide
  have hdescent : baseEnd_2352370 < baseStart_2352370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352396 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 7]
def baseStart_2352396 : Nat := 118140960795 + 2352396 * 2 ^ 59
def prefixEnd_2352396 : Nat := 4983230072969 + 3 ^ 40 * 2352396 * 2
def baseEnd_2352396 : Nat := 268424408380907438562563

theorem tailTrace_2352396 : CollatzResearch.WordTrace tailWord_2352396 prefixEnd_2352396 268424408380907438562563 := by
  unfold tailWord_2352396
  simp only [CollatzResearch.WordTrace]
  refine ⟨42899465392839262048190521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57199287190452349397587361 42899465392839262048190521)
  ·
    refine ⟨32174599044629446536142891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42899465392839262048190521 32174599044629446536142891)
    ·
      refine ⟨48261898566944169804214337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32174599044629446536142891 48261898566944169804214337)
      ·
        refine ⟨36196423925208127353160753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48261898566944169804214337 36196423925208127353160753)
        ·
          refine ⟨27147317943906095514870565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36196423925208127353160753 27147317943906095514870565)
          ·
            refine ⟨5090122114482392909038231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27147317943906095514870565 5090122114482392909038231)
            ·
              refine ⟨7635183171723589363557347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090122114482392909038231 7635183171723589363557347)
              ·
                refine ⟨11452774757585384045336021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635183171723589363557347 11452774757585384045336021)
                ·
                  refine ⟨268424408380907438562563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11452774757585384045336021 268424408380907438562563)
                  ·
                    rfl

theorem cell22_2352396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_2352396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352396 prefixEnd_2352396 := by exact prefixLift 2352396
  have htrace : WordTrace (prefixWord ++ tailWord_2352396) baseStart_2352396 baseEnd_2352396 := by
    simpa [prefixWord, tailWord_2352396, baseEnd_2352396] using wordTrace_append hprefix tailTrace_2352396
  have hstable : (prefixWord ++ tailWord_2352396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352396).length < 2 ^ (prefixWord ++ tailWord_2352396).sum := by decide
  have hdescent : baseEnd_2352396 < baseStart_2352396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352458 : List Nat := [3, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_2352458 : Nat := 118140960795 + 2352458 * 2 ^ 59
def prefixEnd_2352458 : Nat := 4983230072969 + 3 ^ 40 * 2352458 * 2
def baseEnd_2352458 : Nat := 268431483003258273545833

theorem tailTrace_2352458 : CollatzResearch.WordTrace tailWord_2352458 prefixEnd_2352458 268431483003258273545833 := by
  unfold tailWord_2352458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21450298027863477171284507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57200794740969272456758685 21450298027863477171284507)
  ·
    refine ⟨32175447041795215756926761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21450298027863477171284507 32175447041795215756926761)
    ·
      refine ⟨24131585281346411817695071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32175447041795215756926761 24131585281346411817695071)
      ·
        refine ⟨36197377922019617726542607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24131585281346411817695071 36197377922019617726542607)
        ·
          refine ⟨54296066883029426589813911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36197377922019617726542607 54296066883029426589813911)
          ·
            refine ⟨81444100324544139884720867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54296066883029426589813911 81444100324544139884720867)
            ·
              refine ⟨122166150486816209827081301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81444100324544139884720867 122166150486816209827081301)
              ·
                refine ⟨1431634576017377458911109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 122166150486816209827081301 1431634576017377458911109)
                ·
                  refine ⟨268431483003258273545833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1431634576017377458911109 268431483003258273545833)
                  ·
                    rfl

theorem cell22_2352458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_2352458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352458 prefixEnd_2352458 := by exact prefixLift 2352458
  have htrace : WordTrace (prefixWord ++ tailWord_2352458) baseStart_2352458 baseEnd_2352458 := by
    simpa [prefixWord, tailWord_2352458, baseEnd_2352458] using wordTrace_append hprefix tailTrace_2352458
  have hstable : (prefixWord ++ tailWord_2352458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352458).length < 2 ^ (prefixWord ++ tailWord_2352458).sum := by decide
  have hdescent : baseEnd_2352458 < baseStart_2352458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352490 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_2352490 : Nat := 118140960795 + 2352490 * 2 ^ 59
def prefixEnd_2352490 : Nat := 4983230072969 + 3 ^ 40 * 2352490 * 2
def baseEnd_2352490 : Nat := 805305403263737403837401

theorem tailTrace_2352490 : CollatzResearch.WordTrace tailWord_2352490 prefixEnd_2352490 805305403263737403837401 := by
  unfold tailWord_2352490
  simp only [CollatzResearch.WordTrace]
  refine ⟨21450589811834494537575731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57201572831558652100201949 21450589811834494537575731)
  ·
    refine ⟨32175884717751741806363597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21450589811834494537575731 32175884717751741806363597)
    ·
      refine ⟨12065956769156903177386349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32175884717751741806363597 12065956769156903177386349)
      ·
        refine ⟨4524733788433838691519881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12065956769156903177386349 4524733788433838691519881)
        ·
          refine ⟨3393550341325379018639911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4524733788433838691519881 3393550341325379018639911)
          ·
            refine ⟨5090325511988068527959867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393550341325379018639911 5090325511988068527959867)
            ·
              refine ⟨7635488267982102791939801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090325511988068527959867 7635488267982102791939801)
              ·
                refine ⟨5726616200986577093954851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7635488267982102791939801 5726616200986577093954851)
                ·
                  refine ⟨8589924301479865640932277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5726616200986577093954851 8589924301479865640932277)
                  ·
                    refine ⟨805305403263737403837401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8589924301479865640932277 805305403263737403837401)
                    ·
                      rfl

theorem cell22_2352490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_2352490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352490 prefixEnd_2352490 := by exact prefixLift 2352490
  have htrace : WordTrace (prefixWord ++ tailWord_2352490) baseStart_2352490 baseEnd_2352490 := by
    simpa [prefixWord, tailWord_2352490, baseEnd_2352490] using wordTrace_append hprefix tailTrace_2352490
  have hstable : (prefixWord ++ tailWord_2352490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352490).length < 2 ^ (prefixWord ++ tailWord_2352490).sum := by decide
  have hdescent : baseEnd_2352490 < baseStart_2352490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352494 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2352494 : Nat := 118140960795 + 2352494 * 2 ^ 59
def prefixEnd_2352494 : Nat := 4983230072969 + 3 ^ 40 * 2352494 * 2
def baseEnd_2352494 : Nat := 805306772545482726737389

theorem tailTrace_2352494 : CollatzResearch.WordTrace tailWord_2352494 prefixEnd_2352494 805306772545482726737389 := by
  unfold tailWord_2352494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10725313142415435854181067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57201670092882324555632357 10725313142415435854181067)
  ·
    refine ⟨16087969713623153781271601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10725313142415435854181067 16087969713623153781271601)
    ·
      refine ⟨12065977285217365335953701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16087969713623153781271601 12065977285217365335953701)
      ·
        refine ⟨2262370740978256000491319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12065977285217365335953701 2262370740978256000491319)
        ·
          refine ⟨3393556111467384000736979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262370740978256000491319 3393556111467384000736979)
          ·
            refine ⟨5090334167201076001105469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393556111467384000736979 5090334167201076001105469)
            ·
              refine ⟨1908875312700403500414551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5090334167201076001105469 1908875312700403500414551)
              ·
                refine ⟨2863312969050605250621827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1908875312700403500414551 2863312969050605250621827)
                ·
                  refine ⟨4294969453575907875932741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2863312969050605250621827 4294969453575907875932741)
                  ·
                    refine ⟨805306772545482726737389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4294969453575907875932741 805306772545482726737389)
                    ·
                      rfl

theorem cell22_2352494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2352494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352494 prefixEnd_2352494 := by exact prefixLift 2352494
  have htrace : WordTrace (prefixWord ++ tailWord_2352494) baseStart_2352494 baseEnd_2352494 := by
    simpa [prefixWord, tailWord_2352494, baseEnd_2352494] using wordTrace_append hprefix tailTrace_2352494
  have hstable : (prefixWord ++ tailWord_2352494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352494).length < 2 ^ (prefixWord ++ tailWord_2352494).sum := by decide
  have hdescent : baseEnd_2352494 < baseStart_2352494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352565 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 5]
def baseStart_2352565 : Nat := 118140960795 + 2352565 * 2 ^ 59
def prefixEnd_2352565 : Nat := 4983230072969 + 3 ^ 40 * 2352565 * 2
def baseEnd_2352565 : Nat := 268443692432154069404057

theorem tailTrace_2352565 : CollatzResearch.WordTrace tailWord_2352565 prefixEnd_2352565 268443692432154069404057 := by
  unfold tailWord_2352565
  simp only [CollatzResearch.WordTrace]
  refine ⟨85805094722066265959283149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57203396481377510639522099 85805094722066265959283149)
  ·
    refine ⟨32176910520774849734731181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85805094722066265959283149 32176910520774849734731181)
    ·
      refine ⟨12066341445290568650524193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32176910520774849734731181 12066341445290568650524193)
      ·
        refine ⟨9049756083967926487893145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12066341445290568650524193 9049756083967926487893145)
        ·
          refine ⟨6787317062975944865919859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9049756083967926487893145 6787317062975944865919859)
          ·
            refine ⟨10180975594463917298879789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6787317062975944865919859 10180975594463917298879789)
            ·
              refine ⟨3817865847923968987079921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10180975594463917298879789 3817865847923968987079921)
              ·
                refine ⟨2863399385942976740309941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3817865847923968987079921 2863399385942976740309941)
                ·
                  refine ⟨268443692432154069404057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2863399385942976740309941 268443692432154069404057)
                  ·
                    rfl

theorem cell22_2352565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_2352565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352565 prefixEnd_2352565 := by exact prefixLift 2352565
  have htrace : WordTrace (prefixWord ++ tailWord_2352565) baseStart_2352565 baseEnd_2352565 := by
    simpa [prefixWord, tailWord_2352565, baseEnd_2352565] using wordTrace_append hprefix tailTrace_2352565
  have hstable : (prefixWord ++ tailWord_2352565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352565).length < 2 ^ (prefixWord ++ tailWord_2352565).sum := by decide
  have hdescent : baseEnd_2352565 < baseStart_2352565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352580 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2352580 : Nat := 118140960795 + 2352580 * 2 ^ 59
def prefixEnd_2352580 : Nat := 4983230072969 + 3 ^ 40 * 2352580 * 2
def baseEnd_2352580 : Nat := 805336212103007169087125

theorem tailTrace_2352580 : CollatzResearch.WordTrace tailWord_2352580 prefixEnd_2352580 805336212103007169087125 := by
  unfold tailWord_2352580
  simp only [CollatzResearch.WordTrace]
  refine ⟨42902820908505961760539597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57203761211341282347386129 42902820908505961760539597)
  ·
    refine ⟨16088557840689735660202349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42902820908505961760539597 16088557840689735660202349)
    ·
      refine ⟨6033209190258650872575881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16088557840689735660202349 6033209190258650872575881)
      ·
        refine ⟨4524906892693988154431911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6033209190258650872575881 4524906892693988154431911)
        ·
          refine ⟨6787360339040982231647867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4524906892693988154431911 6787360339040982231647867)
          ·
            refine ⟨10181040508561473347471801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6787360339040982231647867 10181040508561473347471801)
            ·
              refine ⟨7635780381421105010603851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10181040508561473347471801 7635780381421105010603851)
              ·
                refine ⟨11453670572131657515905777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635780381421105010603851 11453670572131657515905777)
                ·
                  refine ⟨8590252929098743136929333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11453670572131657515905777 8590252929098743136929333)
                  ·
                    refine ⟨805336212103007169087125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8590252929098743136929333 805336212103007169087125)
                    ·
                      rfl

theorem cell22_2352580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2352580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352580 prefixEnd_2352580 := by exact prefixLift 2352580
  have htrace : WordTrace (prefixWord ++ tailWord_2352580) baseStart_2352580 baseEnd_2352580 := by
    simpa [prefixWord, tailWord_2352580, baseEnd_2352580] using wordTrace_append hprefix tailTrace_2352580
  have hstable : (prefixWord ++ tailWord_2352580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352580).length < 2 ^ (prefixWord ++ tailWord_2352580).sum := by decide
  have hdescent : baseEnd_2352580 < baseStart_2352580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352623 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 4, 4]
def baseStart_2352623 : Nat := 118140960795 + 2352623 * 2 ^ 59
def prefixEnd_2352623 : Nat := 4983230072969 + 3 ^ 40 * 2352623 * 2
def baseEnd_2352623 : Nat := 805350931881769390261993

theorem tailTrace_2352623 : CollatzResearch.WordTrace tailWord_2352623 prefixEnd_2352623 805350931881769390261993 := by
  unfold tailWord_2352623
  simp only [CollatzResearch.WordTrace]
  refine ⟨85807210155856141864894523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57204806770570761243263015 85807210155856141864894523)
  ·
    refine ⟨128710815233784212797341785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85807210155856141864894523 128710815233784212797341785)
    ·
      refine ⟨96533111425338159598006339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128710815233784212797341785 96533111425338159598006339)
      ·
        refine ⟨144799667138007239397009509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96533111425338159598006339 144799667138007239397009509)
        ·
          refine ⟨27149937588376357386939283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144799667138007239397009509 27149937588376357386939283)
          ·
            refine ⟨40724906382564536080408925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27149937588376357386939283 40724906382564536080408925)
            ·
              refine ⟨15271839893461701030153347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40724906382564536080408925 15271839893461701030153347)
              ·
                refine ⟨22907759840192551545230021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15271839893461701030153347 22907759840192551545230021)
                ·
                  refine ⟨4295204970036103414730629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22907759840192551545230021 4295204970036103414730629)
                  ·
                    refine ⟨805350931881769390261993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4295204970036103414730629 805350931881769390261993)
                    ·
                      rfl

theorem cell22_2352623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_2352623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352623 prefixEnd_2352623 := by exact prefixLift 2352623
  have htrace : WordTrace (prefixWord ++ tailWord_2352623) baseStart_2352623 baseEnd_2352623 := by
    simpa [prefixWord, tailWord_2352623, baseEnd_2352623] using wordTrace_append hprefix tailTrace_2352623
  have hstable : (prefixWord ++ tailWord_2352623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352623).length < 2 ^ (prefixWord ++ tailWord_2352623).sum := by decide
  have hdescent : baseEnd_2352623 < baseStart_2352623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352625 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 4, 3]
def baseStart_2352625 : Nat := 118140960795 + 2352625 * 2 ^ 59
def prefixEnd_2352625 : Nat := 4983230072969 + 3 ^ 40 * 2352625 * 2
def baseEnd_2352625 : Nat := 805351616522642051711987

theorem tailTrace_2352625 : CollatzResearch.WordTrace tailWord_2352625 prefixEnd_2352625 805351616522642051711987 := by
  unfold tailWord_2352625
  simp only [CollatzResearch.WordTrace]
  refine ⟨85807283101848896206467329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57204855401232597470978219 85807283101848896206467329)
  ·
    refine ⟨64355462326386672154850497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85807283101848896206467329 64355462326386672154850497)
    ·
      refine ⟨48266596744790004116137873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64355462326386672154850497 48266596744790004116137873)
      ·
        refine ⟨36199947558592503087103405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48266596744790004116137873 36199947558592503087103405)
        ·
          refine ⟨13574980334472188657663777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36199947558592503087103405 13574980334472188657663777)
          ·
            refine ⟨10181235250854141493247833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13574980334472188657663777 10181235250854141493247833)
            ·
              refine ⟨7635926438140606119935875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10181235250854141493247833 7635926438140606119935875)
              ·
                refine ⟨11453889657210909179903813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635926438140606119935875 11453889657210909179903813)
                ·
                  refine ⟨2147604310727045471231965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11453889657210909179903813 2147604310727045471231965)
                  ·
                    refine ⟨805351616522642051711987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147604310727045471231965 805351616522642051711987)
                    ·
                      rfl

theorem cell22_2352625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_2352625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352625 prefixEnd_2352625 := by exact prefixLift 2352625
  have htrace : WordTrace (prefixWord ++ tailWord_2352625) baseStart_2352625 baseEnd_2352625 := by
    simpa [prefixWord, tailWord_2352625, baseEnd_2352625] using wordTrace_append hprefix tailTrace_2352625
  have hstable : (prefixWord ++ tailWord_2352625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352625).length < 2 ^ (prefixWord ++ tailWord_2352625).sum := by decide
  have hdescent : baseEnd_2352625 < baseStart_2352625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352646 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2352646 : Nat := 118140960795 + 2352646 * 2 ^ 59
def prefixEnd_2352646 : Nat := 4983230072969 + 3 ^ 40 * 2352646 * 2
def baseEnd_2352646 : Nat := 805358805251804996936923

theorem tailTrace_2352646 : CollatzResearch.WordTrace tailWord_2352646 prefixEnd_2352646 805358805251804996936923 := by
  unfold tailWord_2352646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681501532336650524780681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57205366023181877861987861 2681501532336650524780681)
  ·
    refine ⟨2011126149252487893585511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2681501532336650524780681 2011126149252487893585511)
    ·
      refine ⟨3016689223878731840378267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2011126149252487893585511 3016689223878731840378267)
      ·
        refine ⟨4525033835818097760567401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3016689223878731840378267 4525033835818097760567401)
        ·
          refine ⟨3393775376863573320425551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4525033835818097760567401 3393775376863573320425551)
          ·
            refine ⟨5090663065295359980638327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393775376863573320425551 5090663065295359980638327)
            ·
              refine ⟨7635994597943039970957491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090663065295359980638327 7635994597943039970957491)
              ·
                refine ⟨11453991896914559956436237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7635994597943039970957491 11453991896914559956436237)
                ·
                  refine ⟨4295246961342959983663589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11453991896914559956436237 4295246961342959983663589)
                  ·
                    refine ⟨805358805251804996936923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4295246961342959983663589 805358805251804996936923)
                    ·
                      rfl

theorem cell22_2352646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2352646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352646 prefixEnd_2352646 := by exact prefixLift 2352646
  have htrace : WordTrace (prefixWord ++ tailWord_2352646) baseStart_2352646 baseEnd_2352646 := by
    simpa [prefixWord, tailWord_2352646, baseEnd_2352646] using wordTrace_append hprefix tailTrace_2352646
  have hstable : (prefixWord ++ tailWord_2352646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352646).length < 2 ^ (prefixWord ++ tailWord_2352646).sum := by decide
  have hdescent : baseEnd_2352646 < baseStart_2352646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352728 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 10]
def baseStart_2352728 : Nat := 118140960795 + 2352728 * 2 ^ 59
def prefixEnd_2352728 : Nat := 4983230072969 + 3 ^ 40 * 2352728 * 2
def baseEnd_2352728 : Nat := 268462291842528038795557

theorem tailTrace_2352728 : CollatzResearch.WordTrace tailWord_2352728 prefixEnd_2352728 268462291842528038795557 := by
  unfold tailWord_2352728
  simp only [CollatzResearch.WordTrace]
  refine ⟨42905519910237872398733419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57207359880317163198311225 42905519910237872398733419)
  ·
    refine ⟨64358279865356808598100129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42905519910237872398733419 64358279865356808598100129)
    ·
      refine ⟨48268709899017606448575097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64358279865356808598100129 48268709899017606448575097)
      ·
        refine ⟨36201532424263204836431323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48268709899017606448575097 36201532424263204836431323)
        ·
          refine ⟨54302298636394807254646985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36201532424263204836431323 54302298636394807254646985)
          ·
            refine ⟨40726723977296105440985239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54302298636394807254646985 40726723977296105440985239)
            ·
              refine ⟨61090085965944158161477859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40726723977296105440985239 61090085965944158161477859)
              ·
                refine ⟨91635128948916237242216789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61090085965944158161477859 91635128948916237242216789)
                ·
                  refine ⟨268462291842528038795557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 91635128948916237242216789 268462291842528038795557)
                  ·
                    rfl

theorem cell22_2352728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_2352728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352728 prefixEnd_2352728 := by exact prefixLift 2352728
  have htrace : WordTrace (prefixWord ++ tailWord_2352728) baseStart_2352728 baseEnd_2352728 := by
    simpa [prefixWord, tailWord_2352728, baseEnd_2352728] using wordTrace_append hprefix tailTrace_2352728
  have hstable : (prefixWord ++ tailWord_2352728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352728).length < 2 ^ (prefixWord ++ tailWord_2352728).sum := by decide
  have hdescent : baseEnd_2352728 < baseStart_2352728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352760 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 8, 3]
def baseStart_2352760 : Nat := 118140960795 + 2352760 * 2 ^ 59
def prefixEnd_2352760 : Nat := 4983230072969 + 3 ^ 40 * 2352760 * 2
def baseEnd_2352760 : Nat := 805397829781546699586573

theorem tailTrace_2352760 : CollatzResearch.WordTrace tailWord_2352760 prefixEnd_2352760 805397829781546699586573 := by
  unfold tailWord_2352760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42906103478179907131315867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57208137970906542841754489 42906103478179907131315867)
  ·
    refine ⟨64359155217269860696973801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42906103478179907131315867 64359155217269860696973801)
    ·
      refine ⟨48269366412952395522730351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64359155217269860696973801 48269366412952395522730351)
      ·
        refine ⟨72404049619428593284095527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48269366412952395522730351 72404049619428593284095527)
        ·
          refine ⟨108606074429142889926143291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72404049619428593284095527 108606074429142889926143291)
          ·
            refine ⟨162909111643714334889214937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108606074429142889926143291 162909111643714334889214937)
            ·
              refine ⟨122181833732785751166911203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162909111643714334889214937 122181833732785751166911203)
              ·
                refine ⟨183272750599178626750366805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122181833732785751166911203 183272750599178626750366805)
                ·
                  refine ⟨2147727546084124532230861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 183272750599178626750366805 2147727546084124532230861)
                  ·
                    refine ⟨805397829781546699586573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147727546084124532230861 805397829781546699586573)
                    ·
                      rfl

theorem cell22_2352760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_2352760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352760 prefixEnd_2352760 := by exact prefixLift 2352760
  have htrace : WordTrace (prefixWord ++ tailWord_2352760) baseStart_2352760 baseEnd_2352760 := by
    simpa [prefixWord, tailWord_2352760, baseEnd_2352760] using wordTrace_append hprefix tailTrace_2352760
  have hstable : (prefixWord ++ tailWord_2352760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352760).length < 2 ^ (prefixWord ++ tailWord_2352760).sum := by decide
  have hdescent : baseEnd_2352760 < baseStart_2352760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352775 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2352775 : Nat := 118140960795 + 2352775 * 2 ^ 59
def prefixEnd_2352775 : Nat := 4983230072969 + 3 ^ 40 * 2352775 * 2
def baseEnd_2352775 : Nat := 805402964588091660461527

theorem tailTrace_2352775 : CollatzResearch.WordTrace tailWord_2352775 prefixEnd_2352775 805402964588091660461527 := by
  unfold tailWord_2352775
  simp only [CollatzResearch.WordTrace]
  refine ⟨85812754051305471824427779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57208502700870314549618519 85812754051305471824427779)
  ·
    refine ⟨128719131076958207736641669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85812754051305471824427779 128719131076958207736641669)
    ·
      refine ⟨24134837076929663950620313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128719131076958207736641669 24134837076929663950620313)
      ·
        refine ⟨18101127807697247962965235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24134837076929663950620313 18101127807697247962965235)
        ·
          refine ⟨27151691711545871944447853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18101127807697247962965235 27151691711545871944447853)
          ·
            refine ⟨10181884391829701979167945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27151691711545871944447853 10181884391829701979167945)
            ·
              refine ⟨7636413293872276484375959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10181884391829701979167945 7636413293872276484375959)
              ·
                refine ⟨11454619940808414726563939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7636413293872276484375959 11454619940808414726563939)
                ·
                  refine ⟨17181929911212622089845909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11454619940808414726563939 17181929911212622089845909)
                  ·
                    refine ⟨805402964588091660461527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17181929911212622089845909 805402964588091660461527)
                    ·
                      rfl

theorem cell22_2352775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2352775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352775 prefixEnd_2352775 := by exact prefixLift 2352775
  have htrace : WordTrace (prefixWord ++ tailWord_2352775) baseStart_2352775 baseEnd_2352775 := by
    simpa [prefixWord, tailWord_2352775, baseEnd_2352775] using wordTrace_append hprefix tailTrace_2352775
  have hstable : (prefixWord ++ tailWord_2352775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352775).length < 2 ^ (prefixWord ++ tailWord_2352775).sum := by decide
  have hdescent : baseEnd_2352775 < baseStart_2352775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352792 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_2352792 : Nat := 118140960795 + 2352792 * 2 ^ 59
def prefixEnd_2352792 : Nat := 4983230072969 + 3 ^ 40 * 2352792 * 2
def baseEnd_2352792 : Nat := 805408784035509282786475

theorem tailTrace_2352792 : CollatzResearch.WordTrace tailWord_2352792 prefixEnd_2352792 805408784035509282786475 := by
  unfold tailWord_2352792
  simp only [CollatzResearch.WordTrace]
  refine ⟨42906687046121941863898315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57208916061495922485197753 42906687046121941863898315)
  ·
    refine ⟨64360030569182912795847473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42906687046121941863898315 64360030569182912795847473)
    ·
      refine ⟨48270022926887184596885605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64360030569182912795847473 48270022926887184596885605)
      ·
        refine ⟨9050629298791347111916051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48270022926887184596885605 9050629298791347111916051)
        ·
          refine ⟨13575943948187020667874077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9050629298791347111916051 13575943948187020667874077)
          ·
            refine ⟨5090978980570132750452779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13575943948187020667874077 5090978980570132750452779)
            ·
              refine ⟨7636468470855199125679169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5090978980570132750452779 7636468470855199125679169)
              ·
                refine ⟨5727351353141399344259377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7636468470855199125679169 5727351353141399344259377)
                ·
                  refine ⟨4295513514856049508194533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5727351353141399344259377 4295513514856049508194533)
                  ·
                    refine ⟨805408784035509282786475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4295513514856049508194533 805408784035509282786475)
                    ·
                      rfl

theorem cell22_2352792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_2352792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352792 prefixEnd_2352792 := by exact prefixLift 2352792
  have htrace : WordTrace (prefixWord ++ tailWord_2352792) baseStart_2352792 baseEnd_2352792 := by
    simpa [prefixWord, tailWord_2352792, baseEnd_2352792] using wordTrace_append hprefix tailTrace_2352792
  have hstable : (prefixWord ++ tailWord_2352792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352792).length < 2 ^ (prefixWord ++ tailWord_2352792).sum := by decide
  have hdescent : baseEnd_2352792 < baseStart_2352792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352796 : List Nat := [2, 2, 3, 2, 3, 1, 3, 2, 4]
def baseStart_2352796 : Nat := 118140960795 + 2352796 * 2 ^ 59
def prefixEnd_2352796 : Nat := 4983230072969 + 3 ^ 40 * 2352796 * 2
def baseEnd_2352796 : Nat := 268470051105751535228821

theorem tailTrace_2352796 : CollatzResearch.WordTrace tailWord_2352796 prefixEnd_2352796 268470051105751535228821 := by
  unfold tailWord_2352796
  simp only [CollatzResearch.WordTrace]
  refine ⟨42906759992114696205471121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57209013322819594940628161 42906759992114696205471121)
  ·
    refine ⟨32180069994086022154103341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42906759992114696205471121 32180069994086022154103341)
    ·
      refine ⟨12067526247782258307788753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32180069994086022154103341 12067526247782258307788753)
      ·
        refine ⟨9050644685836693730841565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12067526247782258307788753 9050644685836693730841565)
        ·
          refine ⟨3393991757188760149065587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9050644685836693730841565 3393991757188760149065587)
          ·
            refine ⟨5090987635783140223598381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3393991757188760149065587 5090987635783140223598381)
            ·
              refine ⟨1909120363418677583849393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5090987635783140223598381 1909120363418677583849393)
              ·
                refine ⟨1431840272564008187887045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909120363418677583849393 1431840272564008187887045)
                ·
                  refine ⟨268470051105751535228821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1431840272564008187887045 268470051105751535228821)
                  ·
                    rfl

theorem cell22_2352796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_2352796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352796 prefixEnd_2352796 := by exact prefixLift 2352796
  have htrace : WordTrace (prefixWord ++ tailWord_2352796) baseStart_2352796 baseEnd_2352796 := by
    simpa [prefixWord, tailWord_2352796, baseEnd_2352796] using wordTrace_append hprefix tailTrace_2352796
  have hstable : (prefixWord ++ tailWord_2352796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352796).length < 2 ^ (prefixWord ++ tailWord_2352796).sum := by decide
  have hdescent : baseEnd_2352796 < baseStart_2352796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352839 : List Nat := [1, 1, 4, 1, 1, 1, 4, 5, 1, 3]
def baseStart_2352839 : Nat := 118140960795 + 2352839 * 2 ^ 59
def prefixEnd_2352839 : Nat := 4983230072969 + 3 ^ 40 * 2352839 * 2
def baseEnd_2352839 : Nat := 805424873096016826861331

theorem tailTrace_2352839 : CollatzResearch.WordTrace tailWord_2352839 prefixEnd_2352839 805424873096016826861331 := by
  unfold tailWord_2352839
  simp only [CollatzResearch.WordTrace]
  refine ⟨85815088323073610754757571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57210058882049073836505047 85815088323073610754757571)
  ·
    refine ⟨128722632484610416132136357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85815088323073610754757571 128722632484610416132136357)
    ·
      refine ⟨24135493590864453024775567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128722632484610416132136357 24135493590864453024775567)
      ·
        refine ⟨36203240386296679537163351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24135493590864453024775567 36203240386296679537163351)
        ·
          refine ⟨54304860579445019305745027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36203240386296679537163351 54304860579445019305745027)
          ·
            refine ⟨81457290869167528958617541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54304860579445019305745027 81457290869167528958617541)
            ·
              refine ⟨15273242037968911679740789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81457290869167528958617541 15273242037968911679740789)
              ·
                refine ⟨1431866441059585469975699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15273242037968911679740789 1431866441059585469975699)
                ·
                  refine ⟨2147799661589378204963549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431866441059585469975699 2147799661589378204963549)
                  ·
                    refine ⟨805424873096016826861331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147799661589378204963549 805424873096016826861331)
                    ·
                      rfl

theorem cell22_2352839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_2352839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352839 prefixEnd_2352839 := by exact prefixLift 2352839
  have htrace : WordTrace (prefixWord ++ tailWord_2352839) baseStart_2352839 baseEnd_2352839 := by
    simpa [prefixWord, tailWord_2352839, baseEnd_2352839] using wordTrace_append hprefix tailTrace_2352839
  have hstable : (prefixWord ++ tailWord_2352839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352839).length < 2 ^ (prefixWord ++ tailWord_2352839).sum := by decide
  have hdescent : baseEnd_2352839 < baseStart_2352839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352882 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_2352882 : Nat := 118140960795 + 2352882 * 2 ^ 59
def prefixEnd_2352882 : Nat := 4983230072969 + 3 ^ 40 * 2352882 * 2
def baseEnd_2352882 : Nat := 805439592874779048036199

theorem tailTrace_2352882 : CollatzResearch.WordTrace tailWord_2352882 prefixEnd_2352882 805439592874779048036199 := by
  unfold tailWord_2352882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21454164165479457274643225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57211104441278552732381933 21454164165479457274643225)
  ·
    refine ⟨16090623124109592955982419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21454164165479457274643225 16090623124109592955982419)
    ·
      refine ⟨24135934686164389433973629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16090623124109592955982419 24135934686164389433973629)
      ·
        refine ⟨9050975507311646037740111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24135934686164389433973629 9050975507311646037740111)
        ·
          refine ⟨13576463260967469056610167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9050975507311646037740111 13576463260967469056610167)
          ·
            refine ⟨20364694891451203584915251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13576463260967469056610167 20364694891451203584915251)
            ·
              refine ⟨30547042337176805377372877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20364694891451203584915251 30547042337176805377372877)
              ·
                refine ⟨11455140876441302016514829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30547042337176805377372877 11455140876441302016514829)
                ·
                  refine ⟨4295677828665488256193061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11455140876441302016514829 4295677828665488256193061)
                  ·
                    refine ⟨805439592874779048036199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4295677828665488256193061 805439592874779048036199)
                    ·
                      rfl

theorem cell22_2352882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_2352882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352882 prefixEnd_2352882 := by exact prefixLift 2352882
  have htrace : WordTrace (prefixWord ++ tailWord_2352882) baseStart_2352882 baseEnd_2352882 := by
    simpa [prefixWord, tailWord_2352882, baseEnd_2352882] using wordTrace_append hprefix tailTrace_2352882
  have hstable : (prefixWord ++ tailWord_2352882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352882).length < 2 ^ (prefixWord ++ tailWord_2352882).sum := by decide
  have hdescent : baseEnd_2352882 < baseStart_2352882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352899 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 1, 4]
def baseStart_2352899 : Nat := 118140960795 + 2352899 * 2 ^ 59
def prefixEnd_2352899 : Nat := 4983230072969 + 3 ^ 40 * 2352899 * 2
def baseEnd_2352899 : Nat := 805445412322196670361147

theorem tailTrace_2352899 : CollatzResearch.WordTrace tailWord_2352899 prefixEnd_2352899 805445412322196670361147 := by
  unfold tailWord_2352899
  simp only [CollatzResearch.WordTrace]
  refine ⟨85817276702856241001941751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57211517801904160667961167 85817276702856241001941751)
  ·
    refine ⟨128725915054284361502912627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85817276702856241001941751 128725915054284361502912627)
    ·
      refine ⟨193088872581426542254368941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128725915054284361502912627 193088872581426542254368941)
      ·
        refine ⟨72408327218034953345388353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193088872581426542254368941 72408327218034953345388353)
        ·
          refine ⟨54306245413526215009041265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72408327218034953345388353 54306245413526215009041265)
          ·
            refine ⟨40729684060144661256780949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54306245413526215009041265 40729684060144661256780949)
            ·
              refine ⟨1909203940319280996411607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40729684060144661256780949 1909203940319280996411607)
              ·
                refine ⟨2863805910478921494617411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1909203940319280996411607 2863805910478921494617411)
                ·
                  refine ⟨4295708865718382241926117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2863805910478921494617411 4295708865718382241926117)
                  ·
                    refine ⟨805445412322196670361147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4295708865718382241926117 805445412322196670361147)
                    ·
                      rfl

theorem cell22_2352899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 4].length) (baseStart_2352899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352899 prefixEnd_2352899 := by exact prefixLift 2352899
  have htrace : WordTrace (prefixWord ++ tailWord_2352899) baseStart_2352899 baseEnd_2352899 := by
    simpa [prefixWord, tailWord_2352899, baseEnd_2352899] using wordTrace_append hprefix tailTrace_2352899
  have hstable : (prefixWord ++ tailWord_2352899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352899).length < 2 ^ (prefixWord ++ tailWord_2352899).sum := by decide
  have hdescent : baseEnd_2352899 < baseStart_2352899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352914 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_2352914 : Nat := 118140960795 + 2352914 * 2 ^ 59
def prefixEnd_2352914 : Nat := 4983230072969 + 3 ^ 40 * 2352914 * 2
def baseEnd_2352914 : Nat := 268483515709580543745367

theorem tailTrace_2352914 : CollatzResearch.WordTrace tailWord_2352914 prefixEnd_2352914 268483515709580543745367 := by
  unfold tailWord_2352914
  simp only [CollatzResearch.WordTrace]
  refine ⟨21454455949450474640934449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57211882531867932375825197 21454455949450474640934449)
  ·
    refine ⟨16090841962087855980700837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21454455949450474640934449 16090841962087855980700837)
    ·
      refine ⟨3017032867891472996381407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16090841962087855980700837 3017032867891472996381407)
      ·
        refine ⟨4525549301837209494572111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3017032867891472996381407 4525549301837209494572111)
        ·
          refine ⟨6788323952755814241858167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525549301837209494572111 6788323952755814241858167)
          ·
            refine ⟨10182485929133721362787251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6788323952755814241858167 10182485929133721362787251)
            ·
              refine ⟨15273728893700582044180877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10182485929133721362787251 15273728893700582044180877)
              ·
                refine ⟨5727648335137718266567829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15273728893700582044180877 5727648335137718266567829)
                ·
                  refine ⟨268483515709580543745367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5727648335137718266567829 268483515709580543745367)
                  ·
                    rfl

theorem cell22_2352914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_2352914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352914 prefixEnd_2352914 := by exact prefixLift 2352914
  have htrace : WordTrace (prefixWord ++ tailWord_2352914) baseStart_2352914 baseEnd_2352914 := by
    simpa [prefixWord, tailWord_2352914, baseEnd_2352914] using wordTrace_append hprefix tailTrace_2352914
  have hstable : (prefixWord ++ tailWord_2352914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352914).length < 2 ^ (prefixWord ++ tailWord_2352914).sum := by decide
  have hdescent : baseEnd_2352914 < baseStart_2352914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352929 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 1, 5]
def baseStart_2352929 : Nat := 118140960795 + 2352929 * 2 ^ 59
def prefixEnd_2352929 : Nat := 4983230072969 + 3 ^ 40 * 2352929 * 2
def baseEnd_2352929 : Nat := 805455681935286592111055

theorem tailTrace_2352929 : CollatzResearch.WordTrace tailWord_2352929 prefixEnd_2352929 805455681935286592111055 := by
  unfold tailWord_2352929
  simp only [CollatzResearch.WordTrace]
  refine ⟨85818370892747556125533841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57212247261831704083689227 85818370892747556125533841)
  ·
    refine ⟨64363778169560667094150381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85818370892747556125533841 64363778169560667094150381)
    ·
      refine ⟨24136416813585250160306393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64363778169560667094150381 24136416813585250160306393)
      ·
        refine ⟨18102312610188937620229795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24136416813585250160306393 18102312610188937620229795)
        ·
          refine ⟨27153468915283406430344693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18102312610188937620229795 27153468915283406430344693)
          ·
            refine ⟨2545637710807819352844815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27153468915283406430344693 2545637710807819352844815)
            ·
              refine ⟨3818456566211729029267223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545637710807819352844815 3818456566211729029267223)
              ·
                refine ⟨5727684849317593543900835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3818456566211729029267223 5727684849317593543900835)
                ·
                  refine ⟨8591527273976390315851253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5727684849317593543900835 8591527273976390315851253)
                  ·
                    refine ⟨805455681935286592111055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8591527273976390315851253 805455681935286592111055)
                    ·
                      rfl

theorem cell22_2352929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_2352929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352929 prefixEnd_2352929 := by exact prefixLift 2352929
  have htrace : WordTrace (prefixWord ++ tailWord_2352929) baseStart_2352929 baseEnd_2352929 := by
    simpa [prefixWord, tailWord_2352929, baseEnd_2352929] using wordTrace_append hprefix tailTrace_2352929
  have hstable : (prefixWord ++ tailWord_2352929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352929).length < 2 ^ (prefixWord ++ tailWord_2352929).sum := by decide
  have hdescent : baseEnd_2352929 < baseStart_2352929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352948 : List Nat := [2, 5, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2352948 : Nat := 118140960795 + 2352948 * 2 ^ 59
def prefixEnd_2352948 : Nat := 4983230072969 + 3 ^ 40 * 2352948 * 2
def baseEnd_2352948 : Nat := 268487395341192291961999

theorem tailTrace_2352948 : CollatzResearch.WordTrace tailWord_2352948 prefixEnd_2352948 268487395341192291961999 := by
  unfold tailWord_2352948
  simp only [CollatzResearch.WordTrace]
  refine ⟨42909531939839361185237749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57212709253119148246983665 42909531939839361185237749)
  ·
    refine ⟨4022768619359940111116039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42909531939839361185237749 4022768619359940111116039)
    ·
      refine ⟨6034152929039910166674059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4022768619359940111116039 6034152929039910166674059)
      ·
        refine ⟨9051229393559865250011089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6034152929039910166674059 9051229393559865250011089)
        ·
          refine ⟨6788422045169898937508317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9051229393559865250011089 6788422045169898937508317)
          ·
            refine ⟨2545658266938712101565619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6788422045169898937508317 2545658266938712101565619)
            ·
              refine ⟨3818487400408068152348429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2545658266938712101565619 3818487400408068152348429)
              ·
                refine ⟨1431932775153025557130661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3818487400408068152348429 1431932775153025557130661)
                ·
                  refine ⟨268487395341192291961999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1431932775153025557130661 268487395341192291961999)
                  ·
                    rfl

theorem cell22_2352948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2352948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352948 prefixEnd_2352948 := by exact prefixLift 2352948
  have htrace : WordTrace (prefixWord ++ tailWord_2352948) baseStart_2352948 baseEnd_2352948 := by
    simpa [prefixWord, tailWord_2352948, baseEnd_2352948] using wordTrace_append hprefix tailTrace_2352948
  have hstable : (prefixWord ++ tailWord_2352948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352948).length < 2 ^ (prefixWord ++ tailWord_2352948).sum := by decide
  have hdescent : baseEnd_2352948 < baseStart_2352948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2352959 : List Nat := [1, 1, 2, 2, 7, 1, 8]
def baseStart_2352959 : Nat := 118140960795 + 2352959 * 2 ^ 59
def prefixEnd_2352959 : Nat := 4983230072969 + 3 ^ 40 * 2352959 * 2
def baseEnd_2352959 : Nat := 29832072279569500513369

theorem tailTrace_2352959 : CollatzResearch.WordTrace tailWord_2352959 prefixEnd_2352959 29832072279569500513369 := by
  unfold tailWord_2352959
  simp only [CollatzResearch.WordTrace]
  refine ⟨85819465082638871249125931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57212976721759247499417287 85819465082638871249125931)
  ·
    refine ⟨128729197623958306873688897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85819465082638871249125931 128729197623958306873688897)
    ·
      refine ⟨96546898217968730155266673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128729197623958306873688897 96546898217968730155266673)
      ·
        refine ⟨72410173663476547616450005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96546898217968730155266673 72410173663476547616450005)
        ·
          refine ⟨1697113445237731584760547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 72410173663476547616450005 1697113445237731584760547)
          ·
            refine ⟨2545670167856597377140821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697113445237731584760547 2545670167856597377140821)
            ·
              refine ⟨29832072279569500513369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2545670167856597377140821 29832072279569500513369)
              ·
                rfl

theorem cell22_2352959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 8].length) (baseStart_2352959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2352959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2352959 prefixEnd_2352959 := by exact prefixLift 2352959
  have htrace : WordTrace (prefixWord ++ tailWord_2352959) baseStart_2352959 baseEnd_2352959 := by
    simpa [prefixWord, tailWord_2352959, baseEnd_2352959] using wordTrace_append hprefix tailTrace_2352959
  have hstable : (prefixWord ++ tailWord_2352959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2352959).length < 2 ^ (prefixWord ++ tailWord_2352959).sum := by decide
  have hdescent : baseEnd_2352959 < baseStart_2352959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2352959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353025 : List Nat := [1, 2, 4, 4, 1, 1, 1, 4, 1, 3]
def baseStart_2353025 : Nat := 118140960795 + 2353025 * 2 ^ 59
def prefixEnd_2353025 : Nat := 4983230072969 + 3 ^ 40 * 2353025 * 2
def baseEnd_2353025 : Nat := 805488544697174341710761

theorem tailTrace_2353025 : CollatzResearch.WordTrace tailWord_2353025 prefixEnd_2353025 805488544697174341710761 := by
  unfold tailWord_2353025
  simp only [CollatzResearch.WordTrace]
  refine ⟨85821872300399764521028529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57214581533599843014019019 85821872300399764521028529)
  ·
    refine ⟨64366404225299823390771397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85821872300399764521028529 64366404225299823390771397)
    ·
      refine ⟨12068700792243716885769637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64366404225299823390771397 12068700792243716885769637)
      ·
        refine ⟨2262881398545696916081807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12068700792243716885769637 2262881398545696916081807)
        ·
          refine ⟨3394322097818545374122711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2262881398545696916081807 3394322097818545374122711)
          ·
            refine ⟨5091483146727818061184067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394322097818545374122711 5091483146727818061184067)
            ·
              refine ⟨7637224720091727091776101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091483146727818061184067 7637224720091727091776101)
              ·
                refine ⟨1431979635017198829708019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7637224720091727091776101 1431979635017198829708019)
                ·
                  refine ⟨2147969452525798244562029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1431979635017198829708019 2147969452525798244562029)
                  ·
                    refine ⟨805488544697174341710761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2147969452525798244562029 805488544697174341710761)
                    ·
                      rfl

theorem cell22_2353025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_2353025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353025 prefixEnd_2353025 := by exact prefixLift 2353025
  have htrace : WordTrace (prefixWord ++ tailWord_2353025) baseStart_2353025 baseEnd_2353025 := by
    simpa [prefixWord, tailWord_2353025, baseEnd_2353025] using wordTrace_append hprefix tailTrace_2353025
  have hstable : (prefixWord ++ tailWord_2353025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353025).length < 2 ^ (prefixWord ++ tailWord_2353025).sum := by decide
  have hdescent : baseEnd_2353025 < baseStart_2353025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353216 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_2353216 : Nat := 118140960795 + 2353216 * 2 ^ 59
def prefixEnd_2353216 : Nat := 4983230072969 + 3 ^ 40 * 2353216 * 2
def baseEnd_2353216 : Nat := 805553927900513510185175

theorem tailTrace_2353216 : CollatzResearch.WordTrace tailWord_2353216 prefixEnd_2353216 805553927900513510185175 := by
  unfold tailWord_2353216
  simp only [CollatzResearch.WordTrace]
  refine ⟨42914419321353902070615751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57219225761805202760821001 42914419321353902070615751)
  ·
    refine ⟨64371628982030853105923627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42914419321353902070615751 64371628982030853105923627)
    ·
      refine ⟨96557443473046279658885441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64371628982030853105923627 96557443473046279658885441)
      ·
        refine ⟨72418082604784709744164081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96557443473046279658885441 72418082604784709744164081)
        ·
          refine ⟨54313561953588532308123061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72418082604784709744164081 54313561953588532308123061)
          ·
            refine ⟨5091896433148924903886537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54313561953588532308123061 5091896433148924903886537)
            ·
              refine ⟨3818922324861693677914903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5091896433148924903886537 3818922324861693677914903)
              ·
                refine ⟨5728383487292540516872355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3818922324861693677914903 5728383487292540516872355)
                ·
                  refine ⟨8592575230938810775308533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5728383487292540516872355 8592575230938810775308533)
                  ·
                    refine ⟨805553927900513510185175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8592575230938810775308533 805553927900513510185175)
                    ·
                      rfl

theorem cell22_2353216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_2353216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353216 prefixEnd_2353216 := by exact prefixLift 2353216
  have htrace : WordTrace (prefixWord ++ tailWord_2353216) baseStart_2353216 baseEnd_2353216 := by
    simpa [prefixWord, tailWord_2353216, baseEnd_2353216] using wordTrace_append hprefix tailTrace_2353216
  have hstable : (prefixWord ++ tailWord_2353216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353216).length < 2 ^ (prefixWord ++ tailWord_2353216).sum := by decide
  have hdescent : baseEnd_2353216 < baseStart_2353216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353250 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2353250 : Nat := 118140960795 + 2353250 * 2 ^ 59
def prefixEnd_2353250 : Nat := 4983230072969 + 3 ^ 40 * 2353250 * 2
def baseEnd_2353250 : Nat := 805565566795348754835071

theorem tailTrace_2353250 : CollatzResearch.WordTrace tailWord_2353250 prefixEnd_2353250 805565566795348754835071 := by
  unfold tailWord_2353250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21457519681146156986992301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57220052483056418631979469 21457519681146156986992301)
  ·
    refine ⟨8046569880429808870122113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21457519681146156986992301 8046569880429808870122113)
    ·
      refine ⟨6034927410322356652591585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8046569880429808870122113 6034927410322356652591585)
      ·
        refine ⟨4526195557741767489443689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6034927410322356652591585 4526195557741767489443689)
        ·
          refine ⟨3394646668306325617082767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4526195557741767489443689 3394646668306325617082767)
          ·
            refine ⟨5091970002459488425624151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3394646668306325617082767 5091970002459488425624151)
            ·
              refine ⟨7637955003689232638436227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5091970002459488425624151 7637955003689232638436227)
              ·
                refine ⟨11456932505533848957654341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7637955003689232638436227 11456932505533848957654341)
                ·
                  refine ⟨2148174844787596679560189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11456932505533848957654341 2148174844787596679560189)
                  ·
                    refine ⟨805565566795348754835071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2148174844787596679560189 805565566795348754835071)
                    ·
                      rfl

theorem cell22_2353250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2353250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353250 prefixEnd_2353250 := by exact prefixLift 2353250
  have htrace : WordTrace (prefixWord ++ tailWord_2353250) baseStart_2353250 baseEnd_2353250 := by
    simpa [prefixWord, tailWord_2353250, baseEnd_2353250] using wordTrace_append hprefix tailTrace_2353250
  have hstable : (prefixWord ++ tailWord_2353250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353250).length < 2 ^ (prefixWord ++ tailWord_2353250).sum := by decide
  have hdescent : baseEnd_2353250 < baseStart_2353250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353312 : List Nat := [2, 1, 1, 4, 2, 3, 3, 2, 1, 3]
def baseStart_2353312 : Nat := 118140960795 + 2353312 * 2 ^ 59
def prefixEnd_2353312 : Nat := 4983230072969 + 3 ^ 40 * 2353312 * 2
def baseEnd_2353312 : Nat := 805586790662401259784881

theorem tailTrace_2353312 : CollatzResearch.WordTrace tailWord_2353312 prefixEnd_2353312 805586790662401259784881 := by
  unfold tailWord_2353312
  simp only [CollatzResearch.WordTrace]
  refine ⟨42916170025180006268363095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57221560033573341691150793 42916170025180006268363095)
  ·
    refine ⟨64374255037770009402544643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42916170025180006268363095 64374255037770009402544643)
    ·
      refine ⟨96561382556655014103816965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64374255037770009402544643 96561382556655014103816965)
      ·
        refine ⟨18105259229372815144465681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96561382556655014103816965 18105259229372815144465681)
        ·
          refine ⟨13578944422029611358349261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18105259229372815144465681 13578944422029611358349261)
          ·
            refine ⟨5092104158261104259380973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13578944422029611358349261 5092104158261104259380973)
            ·
              refine ⟨1909539059347914097267865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5092104158261104259380973 1909539059347914097267865)
              ·
                refine ⟨1432154294510935572950899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909539059347914097267865 1432154294510935572950899)
                ·
                  refine ⟨2148231441766403359426349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1432154294510935572950899 2148231441766403359426349)
                  ·
                    refine ⟨805586790662401259784881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2148231441766403359426349 805586790662401259784881)
                    ·
                      rfl

theorem cell22_2353312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 1, 3].length) (baseStart_2353312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353312 prefixEnd_2353312 := by exact prefixLift 2353312
  have htrace : WordTrace (prefixWord ++ tailWord_2353312) baseStart_2353312 baseEnd_2353312 := by
    simpa [prefixWord, tailWord_2353312, baseEnd_2353312] using wordTrace_append hprefix tailTrace_2353312
  have hstable : (prefixWord ++ tailWord_2353312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353312).length < 2 ^ (prefixWord ++ tailWord_2353312).sum := by decide
  have hdescent : baseEnd_2353312 < baseStart_2353312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353325 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 5]
def baseStart_2353325 : Nat := 118140960795 + 2353325 * 2 ^ 59
def prefixEnd_2353325 : Nat := 4983230072969 + 3 ^ 40 * 2353325 * 2
def baseEnd_2353325 : Nat := 268530413609357853069947

theorem tailTrace_2353325 : CollatzResearch.WordTrace tailWord_2353325 prefixEnd_2353325 268530413609357853069947 := by
  unfold tailWord_2353325
  simp only [CollatzResearch.WordTrace]
  refine ⟨85832814199312915756949429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57221876132875277171299619 85832814199312915756949429)
  ·
    refine ⟨8046826331185585852214009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85832814199312915756949429 8046826331185585852214009)
    ·
      refine ⟨6035119748389189389160507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8046826331185585852214009 6035119748389189389160507)
      ·
        refine ⟨9052679622583784083740761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6035119748389189389160507 9052679622583784083740761)
        ·
          refine ⟨6789509716937838062805571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9052679622583784083740761 6789509716937838062805571)
          ·
            refine ⟨10184264575406757094208357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6789509716937838062805571 10184264575406757094208357)
            ·
              refine ⟨1909549607888766955164067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10184264575406757094208357 1909549607888766955164067)
              ·
                refine ⟨2864324411833150432746101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1909549607888766955164067 2864324411833150432746101)
                ·
                  refine ⟨268530413609357853069947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2864324411833150432746101 268530413609357853069947)
                  ·
                    rfl

theorem cell22_2353325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_2353325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353325 prefixEnd_2353325 := by exact prefixLift 2353325
  have htrace : WordTrace (prefixWord ++ tailWord_2353325) baseStart_2353325 baseEnd_2353325 := by
    simpa [prefixWord, tailWord_2353325, baseEnd_2353325] using wordTrace_append hprefix tailTrace_2353325
  have hstable : (prefixWord ++ tailWord_2353325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353325).length < 2 ^ (prefixWord ++ tailWord_2353325).sum := by decide
  have hdescent : baseEnd_2353325 < baseStart_2353325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353338 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_2353338 : Nat := 118140960795 + 2353338 * 2 ^ 59
def prefixEnd_2353338 : Nat := 4983230072969 + 3 ^ 40 * 2353338 * 2
def baseEnd_2353338 : Nat := 805595690993745858634801

theorem tailTrace_2353338 : CollatzResearch.WordTrace tailWord_2353338 prefixEnd_2353338 805595690993745858634801 := by
  unfold tailWord_2353338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21458322087066454744293167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57222192232177212651448445 21458322087066454744293167)
  ·
    refine ⟨32187483130599682116439751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21458322087066454744293167 32187483130599682116439751)
    ·
      refine ⟨48281224695899523174659627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32187483130599682116439751 48281224695899523174659627)
      ·
        refine ⟨72421837043849284761989441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48281224695899523174659627 72421837043849284761989441)
        ·
          refine ⟨54316377782886963571492081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72421837043849284761989441 54316377782886963571492081)
          ·
            refine ⟨40737283337165222678619061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54316377782886963571492081 40737283337165222678619061)
            ·
              refine ⟨3819120312859239626120537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40737283337165222678619061 3819120312859239626120537)
              ·
                refine ⟨2864340234644429719590403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3819120312859239626120537 2864340234644429719590403)
                ·
                  refine ⟨4296510351966644579385605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864340234644429719590403 4296510351966644579385605)
                  ·
                    refine ⟨805595690993745858634801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4296510351966644579385605 805595690993745858634801)
                    ·
                      rfl

theorem cell22_2353338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_2353338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353338 prefixEnd_2353338 := by exact prefixLift 2353338
  have htrace : WordTrace (prefixWord ++ tailWord_2353338) baseStart_2353338 baseEnd_2353338 := by
    simpa [prefixWord, tailWord_2353338, baseEnd_2353338] using wordTrace_append hprefix tailTrace_2353338
  have hstable : (prefixWord ++ tailWord_2353338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353338).length < 2 ^ (prefixWord ++ tailWord_2353338).sum := by decide
  have hdescent : baseEnd_2353338 < baseStart_2353338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353370 : List Nat := [3, 1, 1, 2, 2, 1, 6, 2, 4]
def baseStart_2353370 : Nat := 118140960795 + 2353370 * 2 ^ 59
def prefixEnd_2353370 : Nat := 4983230072969 + 3 ^ 40 * 2353370 * 2
def baseEnd_2353370 : Nat := 268535548415902813944901

theorem tailTrace_2353370 : CollatzResearch.WordTrace tailWord_2353370 prefixEnd_2353370 268535548415902813944901 := by
  unfold tailWord_2353370
  simp only [CollatzResearch.WordTrace]
  refine ⟨21458613871037472110584391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57222970322766592294891709 21458613871037472110584391)
  ·
    refine ⟨32187920806556208165876587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21458613871037472110584391 32187920806556208165876587)
    ·
      refine ⟨48281881209834312248814881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32187920806556208165876587 48281881209834312248814881)
      ·
        refine ⟨36211410907375734186611161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48281881209834312248814881 36211410907375734186611161)
        ·
          refine ⟨27158558180531800639958371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36211410907375734186611161 27158558180531800639958371)
          ·
            refine ⟨40737837270797700959937557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27158558180531800639958371 40737837270797700959937557)
            ·
              refine ⟨1909586122068642232497073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40737837270797700959937557 1909586122068642232497073)
              ·
                refine ⟨1432189591551481674372805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909586122068642232497073 1432189591551481674372805)
                ·
                  refine ⟨268535548415902813944901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432189591551481674372805 268535548415902813944901)
                  ·
                    rfl

theorem cell22_2353370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_2353370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353370 prefixEnd_2353370 := by exact prefixLift 2353370
  have htrace : WordTrace (prefixWord ++ tailWord_2353370) baseStart_2353370 baseEnd_2353370 := by
    simpa [prefixWord, tailWord_2353370, baseEnd_2353370] using wordTrace_append hprefix tailTrace_2353370
  have hstable : (prefixWord ++ tailWord_2353370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353370).length < 2 ^ (prefixWord ++ tailWord_2353370).sum := by decide
  have hdescent : baseEnd_2353370 < baseStart_2353370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353488 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 6]
def baseStart_2353488 : Nat := 118140960795 + 2353488 * 2 ^ 59
def prefixEnd_2353488 : Nat := 4983230072969 + 3 ^ 40 * 2353488 * 2
def baseEnd_2353488 : Nat := 268549013019731822461447

theorem tailTrace_2353488 : CollatzResearch.WordTrace tailWord_2353488 prefixEnd_2353488 268549013019731822461447 := by
  unfold tailWord_2353488
  simp only [CollatzResearch.WordTrace]
  refine ⟨42919379648861197297566559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57225839531814929730088745 42919379648861197297566559)
  ·
    refine ⟨64379069473291795946349839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42919379648861197297566559 64379069473291795946349839)
    ·
      refine ⟨96568604209937693919524759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64379069473291795946349839 96568604209937693919524759)
      ·
        refine ⟨144852906314906540879287139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96568604209937693919524759 144852906314906540879287139)
        ·
          refine ⟨217279359472359811318930709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144852906314906540879287139 217279359472359811318930709)
          ·
            refine ⟨10184969975266866155574877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 217279359472359811318930709 10184969975266866155574877)
            ·
              refine ⟨3819363740725074808340579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10184969975266866155574877 3819363740725074808340579)
              ·
                refine ⟨5729045611087612212510869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3819363740725074808340579 5729045611087612212510869)
                ·
                  refine ⟨268549013019731822461447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5729045611087612212510869 268549013019731822461447)
                  ·
                    rfl

theorem cell22_2353488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_2353488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353488 prefixEnd_2353488 := by exact prefixLift 2353488
  have htrace : WordTrace (prefixWord ++ tailWord_2353488) baseStart_2353488 baseEnd_2353488 := by
    simpa [prefixWord, tailWord_2353488, baseEnd_2353488] using wordTrace_append hprefix tailTrace_2353488
  have hstable : (prefixWord ++ tailWord_2353488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353488).length < 2 ^ (prefixWord ++ tailWord_2353488).sum := by decide
  have hdescent : baseEnd_2353488 < baseStart_2353488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353537 : List Nat := [1, 2, 4, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2353537 : Nat := 118140960795 + 2353537 * 2 ^ 59
def prefixEnd_2353537 : Nat := 4983230072969 + 3 ^ 40 * 2353537 * 2
def baseEnd_2353537 : Nat := 805663812760575672909191

theorem tailTrace_2353537 : CollatzResearch.WordTrace tailWord_2353537 prefixEnd_2353537 805663812760575672909191 := by
  unfold tailWord_2353537
  simp only [CollatzResearch.WordTrace]
  refine ⟨85840546474544875963666865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57227030983029917309111243 85840546474544875963666865)
  ·
    refine ⟨64380409855908656972750149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85840546474544875963666865 64380409855908656972750149)
    ·
      refine ⟨12071326847982873182390653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64380409855908656972750149 12071326847982873182390653)
      ·
        refine ⟨4526747567993577443396495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12071326847982873182390653 4526747567993577443396495)
        ·
          refine ⟨6790121351990366165094743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526747567993577443396495 6790121351990366165094743)
          ·
            refine ⟨10185182027985549247642115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6790121351990366165094743 10185182027985549247642115)
            ·
              refine ⟨15277773041978323871463173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10185182027985549247642115 15277773041978323871463173)
              ·
                refine ⟨2864582445370935725899345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15277773041978323871463173 2864582445370935725899345)
                ·
                  refine ⟨2148436834028201794424509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2864582445370935725899345 2148436834028201794424509)
                  ·
                    refine ⟨805663812760575672909191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2148436834028201794424509 805663812760575672909191)
                    ·
                      rfl

theorem cell22_2353537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2353537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353537 prefixEnd_2353537 := by exact prefixLift 2353537
  have htrace : WordTrace (prefixWord ++ tailWord_2353537) baseStart_2353537 baseEnd_2353537 := by
    simpa [prefixWord, tailWord_2353537, baseEnd_2353537] using wordTrace_append hprefix tailTrace_2353537
  have hstable : (prefixWord ++ tailWord_2353537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353537).length < 2 ^ (prefixWord ++ tailWord_2353537).sum := by decide
  have hdescent : baseEnd_2353537 < baseStart_2353537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353539 : List Nat := [1, 1, 1, 3, 6, 2, 2, 2, 4]
def baseStart_2353539 : Nat := 118140960795 + 2353539 * 2 ^ 59
def prefixEnd_2353539 : Nat := 4983230072969 + 3 ^ 40 * 2353539 * 2
def baseEnd_2353539 : Nat := 268554832467149444786395

theorem tailTrace_2353539 : CollatzResearch.WordTrace tailWord_2353539 prefixEnd_2353539 268554832467149444786395 := by
  unfold tailWord_2353539
  simp only [CollatzResearch.WordTrace]
  refine ⟨85840619420537630305239671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57227079613691753536826447 85840619420537630305239671)
  ·
    refine ⟨128760929130806445457859507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85840619420537630305239671 128760929130806445457859507)
    ·
      refine ⟨193141393696209668186789261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128760929130806445457859507 193141393696209668186789261)
      ·
        refine ⟨72428022636078625570045973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193141393696209668186789261 72428022636078625570045973)
        ·
          refine ⟨3395063561066185573595905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72428022636078625570045973 3395063561066185573595905)
          ·
            refine ⟨2546297670799639180196929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3395063561066185573595905 2546297670799639180196929)
            ·
              refine ⟨1909723253099729385147697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2546297670799639180196929 1909723253099729385147697)
              ·
                refine ⟨1432292439824797038860773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1909723253099729385147697 1432292439824797038860773)
                ·
                  refine ⟨268554832467149444786395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432292439824797038860773 268554832467149444786395)
                  ·
                    rfl

theorem cell22_2353539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 4].length) (baseStart_2353539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353539 prefixEnd_2353539 := by exact prefixLift 2353539
  have htrace : WordTrace (prefixWord ++ tailWord_2353539) baseStart_2353539 baseEnd_2353539 := by
    simpa [prefixWord, tailWord_2353539, baseEnd_2353539] using wordTrace_append hprefix tailTrace_2353539
  have hstable : (prefixWord ++ tailWord_2353539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353539).length < 2 ^ (prefixWord ++ tailWord_2353539).sum := by decide
  have hdescent : baseEnd_2353539 < baseStart_2353539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353550 : List Nat := [4, 1, 1, 4, 1, 1, 3, 7]
def baseStart_2353550 : Nat := 118140960795 + 2353550 * 2 ^ 59
def prefixEnd_2353550 : Nat := 4983230072969 + 3 ^ 40 * 2353550 * 2
def baseEnd_2353550 : Nat := 89518695880694219148239

theorem tailTrace_2353550 : CollatzResearch.WordTrace tailWord_2353550 prefixEnd_2353550 89518695880694219148239 := by
  unfold tailWord_2353550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10730127577937222397986263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57227347082331852789260069 10730127577937222397986263)
  ·
    refine ⟨16095191366905833596979395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10730127577937222397986263 16095191366905833596979395)
    ·
      refine ⟨24142787050358750395469093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16095191366905833596979395 24142787050358750395469093)
      ·
        refine ⟨4526772571942265699150455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24142787050358750395469093 4526772571942265699150455)
        ·
          refine ⟨6790158857913398548725683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4526772571942265699150455 6790158857913398548725683)
          ·
            refine ⟨10185238286870097823088525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6790158857913398548725683 10185238286870097823088525)
            ·
              refine ⟨3819464357576286683658197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10185238286870097823088525 3819464357576286683658197)
              ·
                refine ⟨89518695880694219148239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3819464357576286683658197 89518695880694219148239)
                ·
                  rfl

theorem cell22_2353550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_2353550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353550 prefixEnd_2353550 := by exact prefixLift 2353550
  have htrace : WordTrace (prefixWord ++ tailWord_2353550) baseStart_2353550 baseEnd_2353550 := by
    simpa [prefixWord, tailWord_2353550, baseEnd_2353550] using wordTrace_append hprefix tailTrace_2353550
  have hstable : (prefixWord ++ tailWord_2353550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353550).length < 2 ^ (prefixWord ++ tailWord_2353550).sum := by decide
  have hdescent : baseEnd_2353550 < baseStart_2353550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353569 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 2, 4]
def baseStart_2353569 : Nat := 118140960795 + 2353569 * 2 ^ 59
def prefixEnd_2353569 : Nat := 4983230072969 + 3 ^ 40 * 2353569 * 2
def baseEnd_2353569 : Nat := 805674767014538256109093

theorem tailTrace_2353569 : CollatzResearch.WordTrace tailWord_2353569 prefixEnd_2353569 805674767014538256109093 := by
  unfold tailWord_2353569
  simp only [CollatzResearch.WordTrace]
  refine ⟨85841713610428945428831761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57227809073619296952554507 85841713610428945428831761)
  ·
    refine ⟨64381285207821709071623821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85841713610428945428831761 64381285207821709071623821)
    ·
      refine ⟨24142981952933140901858933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64381285207821709071623821 24142981952933140901858933)
      ·
        refine ⟨2263404558087481959549275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24142981952933140901858933 2263404558087481959549275)
        ·
          refine ⟨3395106837131222939323913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263404558087481959549275 3395106837131222939323913)
          ·
            refine ⟨2546330127848417204492935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3395106837131222939323913 2546330127848417204492935)
            ·
              refine ⟨3819495191772625806739403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546330127848417204492935 3819495191772625806739403)
              ·
                refine ⟨5729242787658938710109105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3819495191772625806739403 5729242787658938710109105)
                ·
                  refine ⟨4296932090744204032581829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5729242787658938710109105 4296932090744204032581829)
                  ·
                    refine ⟨805674767014538256109093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4296932090744204032581829 805674767014538256109093)
                    ·
                      rfl

theorem cell22_2353569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_2353569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353569 prefixEnd_2353569 := by exact prefixLift 2353569
  have htrace : WordTrace (prefixWord ++ tailWord_2353569) baseStart_2353569 baseEnd_2353569 := by
    simpa [prefixWord, tailWord_2353569, baseEnd_2353569] using wordTrace_append hprefix tailTrace_2353569
  have hstable : (prefixWord ++ tailWord_2353569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353569).length < 2 ^ (prefixWord ++ tailWord_2353569).sum := by decide
  have hdescent : baseEnd_2353569 < baseStart_2353569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353588 : List Nat := [2, 5, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2353588 : Nat := 118140960795 + 2353588 * 2 ^ 59
def prefixEnd_2353588 : Nat := 4983230072969 + 3 ^ 40 * 2353588 * 2
def baseEnd_2353588 : Nat := 805681271102828539884035

theorem tailTrace_2353588 : CollatzResearch.WordTrace tailWord_2353588 prefixEnd_2353588 805681271102828539884035 := by
  unfold tailWord_2353588
  simp only [CollatzResearch.WordTrace]
  refine ⟨42921203298680055836886709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57228271064906741115848945 42921203298680055836886709)
  ·
    refine ⟨4023862809251255234708129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42921203298680055836886709 4023862809251255234708129)
    ·
      refine ⟨3017897106938441426031097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4023862809251255234708129 3017897106938441426031097)
      ·
        refine ⟨2263422830203831069523323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3017897106938441426031097 2263422830203831069523323)
        ·
          refine ⟨3395134245305746604284985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263422830203831069523323 3395134245305746604284985)
          ·
            refine ⟨2546350683979309953213739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3395134245305746604284985 2546350683979309953213739)
            ·
              refine ⟨3819526025968964929820609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546350683979309953213739 3819526025968964929820609)
              ·
                refine ⟨2864644519476723697365457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3819526025968964929820609 2864644519476723697365457)
                ·
                  refine ⟨2148483389607542773024093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2864644519476723697365457 2148483389607542773024093)
                  ·
                    refine ⟨805681271102828539884035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2148483389607542773024093 805681271102828539884035)
                    ·
                      rfl

theorem cell22_2353588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2353588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353588 prefixEnd_2353588 := by exact prefixLift 2353588
  have htrace : WordTrace (prefixWord ++ tailWord_2353588) baseStart_2353588 baseEnd_2353588 := by
    simpa [prefixWord, tailWord_2353588, baseEnd_2353588] using wordTrace_append hprefix tailTrace_2353588
  have hstable : (prefixWord ++ tailWord_2353588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353588).length < 2 ^ (prefixWord ++ tailWord_2353588).sum := by decide
  have hdescent : baseEnd_2353588 < baseStart_2353588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353642 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_2353642 : Nat := 118140960795 + 2353642 * 2 ^ 59
def prefixEnd_2353642 : Nat := 4983230072969 + 3 ^ 40 * 2353642 * 2
def baseEnd_2353642 : Nat := 805699756406390399033869

theorem tailTrace_2353642 : CollatzResearch.WordTrace tailWord_2353642 prefixEnd_2353642 805699756406390399033869 := by
  unfold tailWord_2353642
  simp only [CollatzResearch.WordTrace]
  refine ⟨21461094034791119724059795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57229584092776319264159453 21461094034791119724059795)
  ·
    refine ⟨32191641052186679586089693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21461094034791119724059795 32191641052186679586089693)
    ·
      refine ⟨12071865394570004844783635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32191641052186679586089693 12071865394570004844783635)
      ·
        refine ⟨18107798091855007267175453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12071865394570004844783635 18107798091855007267175453)
        ·
          refine ⟨6790424284445627725190795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18107798091855007267175453 6790424284445627725190795)
          ·
            refine ⟨10185636426668441587786193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6790424284445627725190795 10185636426668441587786193)
            ·
              refine ⟨7639227320001331190839645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10185636426668441587786193 7639227320001331190839645)
              ·
                refine ⟨2864710245000499196564867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7639227320001331190839645 2864710245000499196564867)
                ·
                  refine ⟨4297065367500748794847301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864710245000499196564867 4297065367500748794847301)
                  ·
                    refine ⟨805699756406390399033869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4297065367500748794847301 805699756406390399033869)
                    ·
                      rfl

theorem cell22_2353642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_2353642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353642 prefixEnd_2353642 := by exact prefixLift 2353642
  have htrace : WordTrace (prefixWord ++ tailWord_2353642) baseStart_2353642 baseEnd_2353642 := by
    simpa [prefixWord, tailWord_2353642, baseEnd_2353642] using wordTrace_append hprefix tailTrace_2353642
  have hstable : (prefixWord ++ tailWord_2353642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353642).length < 2 ^ (prefixWord ++ tailWord_2353642).sum := by decide
  have hdescent : baseEnd_2353642 < baseStart_2353642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353717 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2353717 : Nat := 118140960795 + 2353717 * 2 ^ 59
def prefixEnd_2353717 : Nat := 4983230072969 + 3 ^ 40 * 2353717 * 2
def baseEnd_2353717 : Nat := 805725430439115203408639

theorem tailTrace_2353717 : CollatzResearch.WordTrace tailWord_2353717 prefixEnd_2353717 805725430439115203408639 := by
  unfold tailWord_2353717
  simp only [CollatzResearch.WordTrace]
  refine ⟨85847111613892766705219405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57231407742595177803479603 85847111613892766705219405)
  ·
    refine ⟨32192666855209787514457277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85847111613892766705219405 32192666855209787514457277)
    ·
      refine ⟨12072250070703670317921479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32192666855209787514457277 12072250070703670317921479)
      ·
        refine ⟨18108375106055505476882219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12072250070703670317921479 18108375106055505476882219)
        ·
          refine ⟨27162562659083258215323329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18108375106055505476882219 27162562659083258215323329)
          ·
            refine ⟨20371921994312443661492497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27162562659083258215323329 20371921994312443661492497)
            ·
              refine ⟨15278941495734332746119373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20371921994312443661492497 15278941495734332746119373)
              ·
                refine ⟨5729603060900374779794765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15278941495734332746119373 5729603060900374779794765)
                ·
                  refine ⟨2148601147837640542423037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5729603060900374779794765 2148601147837640542423037)
                  ·
                    refine ⟨805725430439115203408639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2148601147837640542423037 805725430439115203408639)
                    ·
                      rfl

theorem cell22_2353717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2353717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353717 prefixEnd_2353717 := by exact prefixLift 2353717
  have htrace : WordTrace (prefixWord ++ tailWord_2353717) baseStart_2353717 baseEnd_2353717 := by
    simpa [prefixWord, tailWord_2353717, baseEnd_2353717] using wordTrace_append hprefix tailTrace_2353717
  have hstable : (prefixWord ++ tailWord_2353717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353717).length < 2 ^ (prefixWord ++ tailWord_2353717).sum := by decide
  have hdescent : baseEnd_2353717 < baseStart_2353717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353775 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 6]
def baseStart_2353775 : Nat := 118140960795 + 2353775 * 2 ^ 59
def prefixEnd_2353775 : Nat := 4983230072969 + 3 ^ 40 * 2353775 * 2
def baseEnd_2353775 : Nat := 268581761674807461819487

theorem tailTrace_2353775 : CollatzResearch.WordTrace tailWord_2353775 prefixEnd_2353775 268581761674807461819487 := by
  unfold tailWord_2353775
  simp only [CollatzResearch.WordTrace]
  refine ⟨85849227047682642610830779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57232818031788428407220519 85849227047682642610830779)
  ·
    refine ⟨128773840571523963916246169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85849227047682642610830779 128773840571523963916246169)
    ·
      refine ⟨96580380428642972937184627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128773840571523963916246169 96580380428642972937184627)
      ·
        refine ⟨144870570642964459405776941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96580380428642972937184627 144870570642964459405776941)
        ·
          refine ⟨54326463991111672277166353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144870570642964459405776941 54326463991111672277166353)
          ·
            refine ⟨40744847993333754207874765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54326463991111672277166353 40744847993333754207874765)
            ·
              refine ⟨15279317997500157827953037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40744847993333754207874765 15279317997500157827953037)
              ·
                refine ⟨5729744249062559185482389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15279317997500157827953037 5729744249062559185482389)
                ·
                  refine ⟨268581761674807461819487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5729744249062559185482389 268581761674807461819487)
                  ·
                    rfl

theorem cell22_2353775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 6].length) (baseStart_2353775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353775 prefixEnd_2353775 := by exact prefixLift 2353775
  have htrace : WordTrace (prefixWord ++ tailWord_2353775) baseStart_2353775 baseEnd_2353775 := by
    simpa [prefixWord, tailWord_2353775, baseEnd_2353775] using wordTrace_append hprefix tailTrace_2353775
  have hstable : (prefixWord ++ tailWord_2353775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353775).length < 2 ^ (prefixWord ++ tailWord_2353775).sum := by decide
  have hdescent : baseEnd_2353775 < baseStart_2353775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353781 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 5]
def baseStart_2353781 : Nat := 118140960795 + 2353781 * 2 ^ 59
def prefixEnd_2353781 : Nat := 4983230072969 + 3 ^ 40 * 2353781 * 2
def baseEnd_2353781 : Nat := 268582446315680123269481

theorem tailTrace_2353781 : CollatzResearch.WordTrace tailWord_2353781 prefixEnd_2353781 268582446315680123269481 := by
  unfold tailWord_2353781
  simp only [CollatzResearch.WordTrace]
  refine ⟨85849445885660905635549197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57232963923773937090366131 85849445885660905635549197)
  ·
    refine ⟨32193542207122839613330949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85849445885660905635549197 32193542207122839613330949)
    ·
      refine ⟨6036289163835532427499553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32193542207122839613330949 6036289163835532427499553)
      ·
        refine ⟨4527216872876649320624665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6036289163835532427499553 4527216872876649320624665)
        ·
          refine ⟨3395412654657486990468499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4527216872876649320624665 3395412654657486990468499)
          ·
            refine ⟨5093118981986230485702749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395412654657486990468499 5093118981986230485702749)
            ·
              refine ⟨1909919618244836432138531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5093118981986230485702749 1909919618244836432138531)
              ·
                refine ⟨2864879427367254648207797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1909919618244836432138531 2864879427367254648207797)
                ·
                  refine ⟨268582446315680123269481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2864879427367254648207797 268582446315680123269481)
                  ·
                    rfl

theorem cell22_2353781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_2353781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353781 prefixEnd_2353781 := by exact prefixLift 2353781
  have htrace : WordTrace (prefixWord ++ tailWord_2353781) baseStart_2353781 baseEnd_2353781 := by
    simpa [prefixWord, tailWord_2353781, baseEnd_2353781] using wordTrace_append hprefix tailTrace_2353781
  have hstable : (prefixWord ++ tailWord_2353781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353781).length < 2 ^ (prefixWord ++ tailWord_2353781).sum := by decide
  have hdescent : baseEnd_2353781 < baseStart_2353781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353837 : List Nat := [1, 5, 2, 1, 1, 2, 1, 9]
def baseStart_2353837 : Nat := 118140960795 + 2353837 * 2 ^ 59
def prefixEnd_2353837 : Nat := 4983230072969 + 3 ^ 40 * 2353837 * 2
def baseEnd_2353837 : Nat := 89529612099052765600919

theorem tailTrace_2353837 : CollatzResearch.WordTrace tailWord_2353837 prefixEnd_2353837 89529612099052765600919 := by
  unfold tailWord_2353837
  simp only [CollatzResearch.WordTrace]
  refine ⟨85851488373458027199587765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57234325582305351466391843 85851488373458027199587765)
  ·
    refine ⟨8048577035011690049961353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85851488373458027199587765 8048577035011690049961353)
    ·
      refine ⟨6036432776258767537471015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8048577035011690049961353 6036432776258767537471015)
      ·
        refine ⟨9054649164388151306206523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6036432776258767537471015 9054649164388151306206523)
        ·
          refine ⟨13581973746582226959309785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9054649164388151306206523 13581973746582226959309785)
          ·
            refine ⟨10186480309936670219482339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13581973746582226959309785 10186480309936670219482339)
            ·
              refine ⟨15279720464905005329223509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10186480309936670219482339 15279720464905005329223509)
              ·
                refine ⟨89529612099052765600919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15279720464905005329223509 89529612099052765600919)
                ·
                  rfl

theorem cell22_2353837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 9].length) (baseStart_2353837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353837 prefixEnd_2353837 := by exact prefixLift 2353837
  have htrace : WordTrace (prefixWord ++ tailWord_2353837) baseStart_2353837 baseEnd_2353837 := by
    simpa [prefixWord, tailWord_2353837, baseEnd_2353837] using wordTrace_append hprefix tailTrace_2353837
  have hstable : (prefixWord ++ tailWord_2353837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353837).length < 2 ^ (prefixWord ++ tailWord_2353837).sum := by decide
  have hdescent : baseEnd_2353837 < baseStart_2353837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353884 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2353884 : Nat := 118140960795 + 2353884 * 2 ^ 59
def prefixEnd_2353884 : Nat := 4983230072969 + 3 ^ 40 * 2353884 * 2
def baseEnd_2353884 : Nat := 805782597951982434483127

theorem tailTrace_2353884 : CollatzResearch.WordTrace tailWord_2353884 prefixEnd_2353884 805782597951982434483127 := by
  unfold tailWord_2353884
  simp only [CollatzResearch.WordTrace]
  refine ⟨42926601302143877113274353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57235468402858502817699137 42926601302143877113274353)
  ·
    refine ⟨32194950976607907834955765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42926601302143877113274353 32194950976607907834955765)
    ·
      refine ⟨3018276654056991359527103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32194950976607907834955765 3018276654056991359527103)
      ·
        refine ⟨4527414981085487039290655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3018276654056991359527103 4527414981085487039290655)
        ·
          refine ⟨6791122471628230558935983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4527414981085487039290655 6791122471628230558935983)
          ·
            refine ⟨10186683707442345838403975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6791122471628230558935983 10186683707442345838403975)
            ·
              refine ⟨15280025561163518757605963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10186683707442345838403975 15280025561163518757605963)
              ·
                refine ⟨22920038341745278136408945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15280025561163518757605963 22920038341745278136408945)
                ·
                  refine ⟨17190028756308958602306709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22920038341745278136408945 17190028756308958602306709)
                  ·
                    refine ⟨805782597951982434483127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17190028756308958602306709 805782597951982434483127)
                    ·
                      rfl

theorem cell22_2353884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2353884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353884 prefixEnd_2353884 := by exact prefixLift 2353884
  have htrace : WordTrace (prefixWord ++ tailWord_2353884) baseStart_2353884 baseEnd_2353884 := by
    simpa [prefixWord, tailWord_2353884, baseEnd_2353884] using wordTrace_append hprefix tailTrace_2353884
  have hstable : (prefixWord ++ tailWord_2353884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353884).length < 2 ^ (prefixWord ++ tailWord_2353884).sum := by decide
  have hdescent : baseEnd_2353884 < baseStart_2353884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353912 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_2353912 : Nat := 118140960795 + 2353912 * 2 ^ 59
def prefixEnd_2353912 : Nat := 4983230072969 + 3 ^ 40 * 2353912 * 2
def baseEnd_2353912 : Nat := 805792182924199694783041

theorem tailTrace_2353912 : CollatzResearch.WordTrace tailWord_2353912 prefixEnd_2353912 805792182924199694783041 := by
  unfold tailWord_2353912
  simp only [CollatzResearch.WordTrace]
  refine ⟨42927111924093157504283995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57236149232124210005711993 42927111924093157504283995)
  ·
    refine ⟨64390667886139736256425993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42927111924093157504283995 64390667886139736256425993)
    ·
      refine ⟨48293000914604802192319495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64390667886139736256425993 48293000914604802192319495)
      ·
        refine ⟨72439501371907203288479243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48293000914604802192319495 72439501371907203288479243)
        ·
          refine ⟨108659252057860804932718865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72439501371907203288479243 108659252057860804932718865)
          ·
            refine ⟨81494439043395603699539149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108659252057860804932718865 81494439043395603699539149)
            ·
              refine ⟨30560414641273351387327181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81494439043395603699539149 30560414641273351387327181)
              ·
                refine ⟨11460155490477506770247693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30560414641273351387327181 11460155490477506770247693)
                ·
                  refine ⟨4297558308929065038842885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11460155490477506770247693 4297558308929065038842885)
                  ·
                    refine ⟨805792182924199694783041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4297558308929065038842885 805792182924199694783041)
                    ·
                      rfl

theorem cell22_2353912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_2353912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353912 prefixEnd_2353912 := by exact prefixLift 2353912
  have htrace : WordTrace (prefixWord ++ tailWord_2353912) baseStart_2353912 baseEnd_2353912 := by
    simpa [prefixWord, tailWord_2353912, baseEnd_2353912] using wordTrace_append hprefix tailTrace_2353912
  have hstable : (prefixWord ++ tailWord_2353912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353912).length < 2 ^ (prefixWord ++ tailWord_2353912).sum := by decide
  have hdescent : baseEnd_2353912 < baseStart_2353912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353957 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_2353957 : Nat := 118140960795 + 2353957 * 2 ^ 59
def prefixEnd_2353957 : Nat := 4983230072969 + 3 ^ 40 * 2353957 * 2
def baseEnd_2353957 : Nat := 805807587343834577407903

theorem tailTrace_2353957 : CollatzResearch.WordTrace tailWord_2353957 prefixEnd_2353957 805807587343834577407903 := by
  unfold tailWord_2353957
  simp only [CollatzResearch.WordTrace]
  refine ⟨85855865133023287693956125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57237243422015525129304083 85855865133023287693956125)
  ·
    refine ⟨32195949424883732885233547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85855865133023287693956125 32195949424883732885233547)
    ·
      refine ⟨48293924137325599327850321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32195949424883732885233547 48293924137325599327850321)
      ·
        refine ⟨36220443102994199495887741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48293924137325599327850321 36220443102994199495887741)
        ·
          refine ⟨13582666163622824810957903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36220443102994199495887741 13582666163622824810957903)
          ·
            refine ⟨20373999245434237216436855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13582666163622824810957903 20373999245434237216436855)
            ·
              refine ⟨30560998868151355824655283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20373999245434237216436855 30560998868151355824655283)
              ·
                refine ⟨45841498302227033736982925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30560998868151355824655283 45841498302227033736982925)
                ·
                  refine ⟨17190561863335137651368597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45841498302227033736982925 17190561863335137651368597)
                  ·
                    refine ⟨805807587343834577407903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17190561863335137651368597 805807587343834577407903)
                    ·
                      rfl

theorem cell22_2353957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_2353957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353957 prefixEnd_2353957 := by exact prefixLift 2353957
  have htrace : WordTrace (prefixWord ++ tailWord_2353957) baseStart_2353957 baseEnd_2353957 := by
    simpa [prefixWord, tailWord_2353957, baseEnd_2353957] using wordTrace_append hprefix tailTrace_2353957
  have hstable : (prefixWord ++ tailWord_2353957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353957).length < 2 ^ (prefixWord ++ tailWord_2353957).sum := by decide
  have hdescent : baseEnd_2353957 < baseStart_2353957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2353978 : List Nat := [3, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_2353978 : Nat := 118140960795 + 2353978 * 2 ^ 59
def prefixEnd_2353978 : Nat := 4983230072969 + 3 ^ 40 * 2353978 * 2
def baseEnd_2353978 : Nat := 268604925357665840877613

theorem tailTrace_2353978 : CollatzResearch.WordTrace tailWord_2353978 prefixEnd_2353978 268604925357665840877613 := by
  unfold tailWord_2353978
  simp only [CollatzResearch.WordTrace]
  refine ⟨21464157766486802070117647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57237754043964805520313725 21464157766486802070117647)
  ·
    refine ⟨32196236649730203105176471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21464157766486802070117647 32196236649730203105176471)
    ·
      refine ⟨48294354974595304657764707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32196236649730203105176471 48294354974595304657764707)
      ·
        refine ⟨72441532461892956986647061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48294354974595304657764707 72441532461892956986647061)
        ·
          refine ⟨3395696834151232358749081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72441532461892956986647061 3395696834151232358749081)
          ·
            refine ⟨2546772625613424269061811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3395696834151232358749081 2546772625613424269061811)
            ·
              refine ⟨3820158938420136403592717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546772625613424269061811 3820158938420136403592717)
              ·
                refine ⟨1432559601907551151347269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3820158938420136403592717 1432559601907551151347269)
                ·
                  refine ⟨268604925357665840877613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432559601907551151347269 268604925357665840877613)
                  ·
                    rfl

theorem cell22_2353978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_2353978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2353978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2353978 prefixEnd_2353978 := by exact prefixLift 2353978
  have htrace : WordTrace (prefixWord ++ tailWord_2353978) baseStart_2353978 baseEnd_2353978 := by
    simpa [prefixWord, tailWord_2353978, baseEnd_2353978] using wordTrace_append hprefix tailTrace_2353978
  have hstable : (prefixWord ++ tailWord_2353978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2353978).length < 2 ^ (prefixWord ++ tailWord_2353978).sum := by decide
  have hdescent : baseEnd_2353978 < baseStart_2353978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2353978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354017 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 9]
def baseStart_2354017 : Nat := 118140960795 + 2354017 * 2 ^ 59
def prefixEnd_2354017 : Nat := 4983230072969 + 3 ^ 40 * 2354017 * 2
def baseEnd_2354017 : Nat := 268609375523338140302573

theorem tailTrace_2354017 : CollatzResearch.WordTrace tailWord_2354017 prefixEnd_2354017 268609375523338140302573 := by
  unfold tailWord_2354017
  simp only [CollatzResearch.WordTrace]
  refine ⟨85858053512805917941140305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57238702341870611960760203 85858053512805917941140305)
  ·
    refine ⟨64393540134604438455855229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85858053512805917941140305 64393540134604438455855229)
    ·
      refine ⟨24147577550476664420945711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64393540134604438455855229 24147577550476664420945711)
      ·
        refine ⟨36221366325714996631418567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24147577550476664420945711 36221366325714996631418567)
        ·
          refine ⟨54332049488572494947127851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36221366325714996631418567 54332049488572494947127851)
          ·
            refine ⟨81498074232858742420691777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54332049488572494947127851 81498074232858742420691777)
            ·
              refine ⟨61123555674644056815518833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81498074232858742420691777 61123555674644056815518833)
              ·
                refine ⟨45842666755983042611639125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61123555674644056815518833 45842666755983042611639125)
                ·
                  refine ⟨268609375523338140302573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45842666755983042611639125 268609375523338140302573)
                  ·
                    rfl

theorem cell22_2354017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_2354017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354017 prefixEnd_2354017 := by exact prefixLift 2354017
  have htrace : WordTrace (prefixWord ++ tailWord_2354017) baseStart_2354017 baseEnd_2354017 := by
    simpa [prefixWord, tailWord_2354017, baseEnd_2354017] using wordTrace_append hprefix tailTrace_2354017
  have hstable : (prefixWord ++ tailWord_2354017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354017).length < 2 ^ (prefixWord ++ tailWord_2354017).sum := by decide
  have hdescent : baseEnd_2354017 < baseStart_2354017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354055 : List Nat := [1, 1, 4, 2, 3, 1, 4, 2, 1, 3]
def baseStart_2354055 : Nat := 118140960795 + 2354055 * 2 ^ 59
def prefixEnd_2354055 : Nat := 4983230072969 + 3 ^ 40 * 2354055 * 2
def baseEnd_2354055 : Nat := 805841134746594988457603

theorem tailTrace_2354055 : CollatzResearch.WordTrace tailWord_2354055 prefixEnd_2354055 805841134746594988457603 := by
  unfold tailWord_2354055
  simp only [CollatzResearch.WordTrace]
  refine ⟨85859439486668250431023619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57239626324445500287349079 85859439486668250431023619)
  ·
    refine ⟨128789159230002375646535429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85859439486668250431023619 128789159230002375646535429)
    ·
      refine ⟨24147967355625445433725393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128789159230002375646535429 24147967355625445433725393)
      ·
        refine ⟨18110975516719084075294045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24147967355625445433725393 18110975516719084075294045)
        ·
          refine ⟨6791615818769656528235267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18110975516719084075294045 6791615818769656528235267)
          ·
            refine ⟨10187423728154484792352901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6791615818769656528235267 10187423728154484792352901)
            ·
              refine ⟨1910141949028965898566169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10187423728154484792352901 1910141949028965898566169)
              ·
                refine ⟨1432606461771724423924627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1910141949028965898566169 1432606461771724423924627)
                ·
                  refine ⟨2148909692657586635886941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1432606461771724423924627 2148909692657586635886941)
                  ·
                    refine ⟨805841134746594988457603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2148909692657586635886941 805841134746594988457603)
                    ·
                      rfl

theorem cell22_2354055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_2354055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354055 prefixEnd_2354055 := by exact prefixLift 2354055
  have htrace : WordTrace (prefixWord ++ tailWord_2354055) baseStart_2354055 baseEnd_2354055 := by
    simpa [prefixWord, tailWord_2354055, baseEnd_2354055] using wordTrace_append hprefix tailTrace_2354055
  have hstable : (prefixWord ++ tailWord_2354055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354055).length < 2 ^ (prefixWord ++ tailWord_2354055).sum := by decide
  have hdescent : baseEnd_2354055 < baseStart_2354055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354079 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 8]
def baseStart_2354079 : Nat := 118140960795 + 2354079 * 2 ^ 59
def prefixEnd_2354079 : Nat := 4983230072969 + 3 ^ 40 * 2354079 * 2
def baseEnd_2354079 : Nat := 268616450145688975285843

theorem tailTrace_2354079 : CollatzResearch.WordTrace tailWord_2354079 prefixEnd_2354079 268616450145688975285843 := by
  unfold tailWord_2354079
  simp only [CollatzResearch.WordTrace]
  refine ⟨85860314838581302529897291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57240209892387535019931527 85860314838581302529897291)
  ·
    refine ⟨128790472257871953794845937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85860314838581302529897291 128790472257871953794845937)
    ·
      refine ⟨96592854193403965346134453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128790472257871953794845937 96592854193403965346134453)
      ·
        refine ⟨9055580080631621751200105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96592854193403965346134453 9055580080631621751200105)
        ·
          refine ⟨6791685060473716313400079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9055580080631621751200105 6791685060473716313400079)
          ·
            refine ⟨10187527590710574470100119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6791685060473716313400079 10187527590710574470100119)
            ·
              refine ⟨15281291386065861705150179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10187527590710574470100119 15281291386065861705150179)
              ·
                refine ⟨22921937079098792557725269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15281291386065861705150179 22921937079098792557725269)
                ·
                  refine ⟨268616450145688975285843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22921937079098792557725269 268616450145688975285843)
                  ·
                    rfl

theorem cell22_2354079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 8].length) (baseStart_2354079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354079 prefixEnd_2354079 := by exact prefixLift 2354079
  have htrace : WordTrace (prefixWord ++ tailWord_2354079) baseStart_2354079 baseEnd_2354079 := by
    simpa [prefixWord, tailWord_2354079, baseEnd_2354079] using wordTrace_append hprefix tailTrace_2354079
  have hstable : (prefixWord ++ tailWord_2354079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354079).length < 2 ^ (prefixWord ++ tailWord_2354079).sum := by decide
  have hdescent : baseEnd_2354079 < baseStart_2354079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354081 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_2354081 : Nat := 118140960795 + 2354081 * 2 ^ 59
def prefixEnd_2354081 : Nat := 4983230072969 + 3 ^ 40 * 2354081 * 2
def baseEnd_2354081 : Nat := 805850035077939587307523

theorem tailTrace_2354081 : CollatzResearch.WordTrace tailWord_2354081 prefixEnd_2354081 805850035077939587307523 := by
  unfold tailWord_2354081
  simp only [CollatzResearch.WordTrace]
  refine ⟨85860387784574056871470097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57240258523049371247646731 85860387784574056871470097)
  ·
    refine ⟨64395290838430542653602573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85860387784574056871470097 64395290838430542653602573)
    ·
      refine ⟨24148234064411453495100965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64395290838430542653602573 24148234064411453495100965)
      ·
        refine ⟨4527793887077147530331431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24148234064411453495100965 4527793887077147530331431)
        ·
          refine ⟨6791690830615721295497147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4527793887077147530331431 6791690830615721295497147)
          ·
            refine ⟨10187536245923581943245721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6791690830615721295497147 10187536245923581943245721)
            ·
              refine ⟨7640652184442686457434291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10187536245923581943245721 7640652184442686457434291)
              ·
                refine ⟨11460978276664029686151437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7640652184442686457434291 11460978276664029686151437)
                ·
                  refine ⟨4297866853749011132306789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11460978276664029686151437 4297866853749011132306789)
                  ·
                    refine ⟨805850035077939587307523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4297866853749011132306789 805850035077939587307523)
                    ·
                      rfl

theorem cell22_2354081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_2354081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354081 prefixEnd_2354081 := by exact prefixLift 2354081
  have htrace : WordTrace (prefixWord ++ tailWord_2354081) baseStart_2354081 baseEnd_2354081 := by
    simpa [prefixWord, tailWord_2354081, baseEnd_2354081] using wordTrace_append hprefix tailTrace_2354081
  have hstable : (prefixWord ++ tailWord_2354081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354081).length < 2 ^ (prefixWord ++ tailWord_2354081).sum := by decide
  have hdescent : baseEnd_2354081 < baseStart_2354081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354111 : List Nat := [1, 1, 2, 2, 2, 1, 2, 6, 2, 3]
def baseStart_2354111 : Nat := 118140960795 + 2354111 * 2 ^ 59
def prefixEnd_2354111 : Nat := 4983230072969 + 3 ^ 40 * 2354111 * 2
def baseEnd_2354111 : Nat := 805860304691029509057431

theorem tailTrace_2354111 : CollatzResearch.WordTrace tailWord_2354111 prefixEnd_2354111 805860304691029509057431 := by
  unfold tailWord_2354111
  simp only [CollatzResearch.WordTrace]
  refine ⟨85861481974465371995062187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57240987982976914663374791 85861481974465371995062187)
  ·
    refine ⟨128792222961698057992593281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85861481974465371995062187 128792222961698057992593281)
    ·
      refine ⟨96594167221273543494444961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128792222961698057992593281 96594167221273543494444961)
      ·
        refine ⟨72445625415955157620833721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96594167221273543494444961 72445625415955157620833721)
        ·
          refine ⟨54334219061966368215625291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72445625415955157620833721 54334219061966368215625291)
          ·
            refine ⟨81501328592949552323437937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54334219061966368215625291 81501328592949552323437937)
            ·
              refine ⟨61125996444712164242578453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81501328592949552323437937 61125996444712164242578453)
              ·
                refine ⟨2865281083345882698870865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61125996444712164242578453 2865281083345882698870865)
                ·
                  refine ⟨2148960812509412024153149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2865281083345882698870865 2148960812509412024153149)
                  ·
                    refine ⟨805860304691029509057431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2148960812509412024153149 805860304691029509057431)
                    ·
                      rfl

theorem cell22_2354111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_2354111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354111 prefixEnd_2354111 := by exact prefixLift 2354111
  have htrace : WordTrace (prefixWord ++ tailWord_2354111) baseStart_2354111 baseEnd_2354111 := by
    simpa [prefixWord, tailWord_2354111, baseEnd_2354111] using wordTrace_append hprefix tailTrace_2354111
  have hstable : (prefixWord ++ tailWord_2354111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354111).length < 2 ^ (prefixWord ++ tailWord_2354111).sum := by decide
  have hdescent : baseEnd_2354111 < baseStart_2354111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354124 : List Nat := [2, 2, 1, 4, 1, 1, 2, 9]
def baseStart_2354124 : Nat := 118140960795 + 2354124 * 2 ^ 59
def prefixEnd_2354124 : Nat := 4983230072969 + 3 ^ 40 * 2354124 * 2
def baseEnd_2354124 : Nat := 89540528317411312053599

theorem tailTrace_2354124 : CollatzResearch.WordTrace tailWord_2354124 prefixEnd_2354124 89540528317411312053599 := by
  unfold tailWord_2354124
  simp only [CollatzResearch.WordTrace]
  refine ⟨42930978061709137607642713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57241304082278850143523617 42930978061709137607642713)
  ·
    refine ⟨32198233546281853205732035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42930978061709137607642713 32198233546281853205732035)
    ·
      refine ⟨48297350319422779808598053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32198233546281853205732035 48297350319422779808598053)
      ·
        refine ⟨9055753184891771214112135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48297350319422779808598053 9055753184891771214112135)
        ·
          refine ⟨13583629777337656821168203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9055753184891771214112135 13583629777337656821168203)
          ·
            refine ⟨20375444666006485231752305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13583629777337656821168203 20375444666006485231752305)
            ·
              refine ⟨15281583499504863923814229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20375444666006485231752305 15281583499504863923814229)
              ·
                refine ⟨89540528317411312053599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15281583499504863923814229 89540528317411312053599)
                ·
                  rfl

theorem cell22_2354124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 9].length) (baseStart_2354124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354124 prefixEnd_2354124 := by exact prefixLift 2354124
  have htrace : WordTrace (prefixWord ++ tailWord_2354124) baseStart_2354124 baseEnd_2354124 := by
    simpa [prefixWord, tailWord_2354124, baseEnd_2354124] using wordTrace_append hprefix tailTrace_2354124
  have hstable : (prefixWord ++ tailWord_2354124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354124).length < 2 ^ (prefixWord ++ tailWord_2354124).sum := by decide
  have hdescent : baseEnd_2354124 < baseStart_2354124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354141 : List Nat := [1, 4, 3, 1, 2, 2, 1, 8]
def baseStart_2354141 : Nat := 118140960795 + 2354141 * 2 ^ 59
def prefixEnd_2354141 : Nat := 4983230072969 + 3 ^ 40 * 2354141 * 2
def baseEnd_2354141 : Nat := 89541174922679936756371

theorem tailTrace_2354141 : CollatzResearch.WordTrace tailWord_2354141 prefixEnd_2354141 89541174922679936756371 := by
  unfold tailWord_2354141
  simp only [CollatzResearch.WordTrace]
  refine ⟨85862576164356687118654277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57241717442904458079102851 85862576164356687118654277)
  ·
    refine ⟨16099233030816878834747677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85862576164356687118654277 16099233030816878834747677)
    ·
      refine ⟨6037212386556329563030379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16099233030816878834747677 6037212386556329563030379)
      ·
        refine ⟨9055818579834494344545569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6037212386556329563030379 9055818579834494344545569)
        ·
          refine ⟨6791863934875870758409177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9055818579834494344545569 6791863934875870758409177)
          ·
            refine ⟨5093897951156903068806883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6791863934875870758409177 5093897951156903068806883)
            ·
              refine ⟨7640846926735354603210325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093897951156903068806883 7640846926735354603210325)
              ·
                refine ⟨89541174922679936756371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7640846926735354603210325 89541174922679936756371)
                ·
                  rfl

theorem cell22_2354141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 8].length) (baseStart_2354141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354141 prefixEnd_2354141 := by exact prefixLift 2354141
  have htrace : WordTrace (prefixWord ++ tailWord_2354141) baseStart_2354141 baseEnd_2354141 := by
    simpa [prefixWord, tailWord_2354141, baseEnd_2354141] using wordTrace_append hprefix tailTrace_2354141
  have hstable : (prefixWord ++ tailWord_2354141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354141).length < 2 ^ (prefixWord ++ tailWord_2354141).sum := by decide
  have hdescent : baseEnd_2354141 < baseStart_2354141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354158 : List Nat := [4, 1, 2, 1, 5, 1, 8]
def baseStart_2354158 : Nat := 118140960795 + 2354158 * 2 ^ 59
def prefixEnd_2354158 : Nat := 4983230072969 + 3 ^ 40 * 2354158 * 2
def baseEnd_2354158 : Nat := 29847273842649520486381

theorem tailTrace_2354158 : CollatzResearch.WordTrace tailWord_2354158 prefixEnd_2354158 29847273842649520486381 := by
  unfold tailWord_2354158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10732899525661887377752891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57242130803530066014682085 10732899525661887377752891)
  ·
    refine ⟨16099349288492831066629337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10732899525661887377752891 16099349288492831066629337)
    ·
      refine ⟨12074511966369623299972003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16099349288492831066629337 12074511966369623299972003)
      ·
        refine ⟨18111767949554434949958005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12074511966369623299972003 18111767949554434949958005)
        ·
          refine ⟨1697978245270728276558563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18111767949554434949958005 1697978245270728276558563)
          ·
            refine ⟨2546967367906092414837845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1697978245270728276558563 2546967367906092414837845)
            ·
              refine ⟨29847273842649520486381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2546967367906092414837845 29847273842649520486381)
              ·
                rfl

theorem cell22_2354158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 8].length) (baseStart_2354158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354158 prefixEnd_2354158 := by exact prefixLift 2354158
  have htrace : WordTrace (prefixWord ++ tailWord_2354158) baseStart_2354158 baseEnd_2354158 := by
    simpa [prefixWord, tailWord_2354158, baseEnd_2354158] using wordTrace_append hprefix tailTrace_2354158
  have hstable : (prefixWord ++ tailWord_2354158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354158).length < 2 ^ (prefixWord ++ tailWord_2354158).sum := by decide
  have hdescent : baseEnd_2354158 < baseStart_2354158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354164 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2354164 : Nat := 118140960795 + 2354164 * 2 ^ 59
def prefixEnd_2354164 : Nat := 4983230072969 + 3 ^ 40 * 2354164 * 2
def baseEnd_2354164 : Nat := 268626149224718345827423

theorem tailTrace_2354164 : CollatzResearch.WordTrace tailWord_2354164 prefixEnd_2354164 268626149224718345827423 := by
  unfold tailWord_2354164
  simp only [CollatzResearch.WordTrace]
  refine ⟨42931707521636681023370773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57242276695515574697827697 42931707521636681023370773)
  ·
    refine ⟨2012423790076719422970505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42931707521636681023370773 2012423790076719422970505)
    ·
      refine ⟨1509317842557539567227879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2012423790076719422970505 1509317842557539567227879)
      ·
        refine ⟨2263976763836309350841819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509317842557539567227879 2263976763836309350841819)
        ·
          refine ⟨3395965145754464026262729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263976763836309350841819 3395965145754464026262729)
          ·
            refine ⟨2546973859315848019697047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3395965145754464026262729 2546973859315848019697047)
            ·
              refine ⟨3820460788973772029545571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2546973859315848019697047 3820460788973772029545571)
              ·
                refine ⟨5730691183460658044318357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3820460788973772029545571 5730691183460658044318357)
                ·
                  refine ⟨268626149224718345827423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5730691183460658044318357 268626149224718345827423)
                  ·
                    rfl

theorem cell22_2354164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2354164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354164 prefixEnd_2354164 := by exact prefixLift 2354164
  have htrace : WordTrace (prefixWord ++ tailWord_2354164) baseStart_2354164 baseEnd_2354164 := by
    simpa [prefixWord, tailWord_2354164, baseEnd_2354164] using wordTrace_append hprefix tailTrace_2354164
  have hstable : (prefixWord ++ tailWord_2354164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354164).length < 2 ^ (prefixWord ++ tailWord_2354164).sum := by decide
  have hdescent : baseEnd_2354164 < baseStart_2354164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354169 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 7]
def baseStart_2354169 : Nat := 118140960795 + 2354169 * 2 ^ 59
def prefixEnd_2354169 : Nat := 4983230072969 + 3 ^ 40 * 2354169 * 2
def baseEnd_2354169 : Nat := 268626719758778897035751

theorem tailTrace_2354169 : CollatzResearch.WordTrace tailWord_2354169 prefixEnd_2354169 268626719758778897035751 := by
  unfold tailWord_2354169
  simp only [CollatzResearch.WordTrace]
  refine ⟨85863597408255247900673561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57242398272170165267115707 85863597408255247900673561)
  ·
    refine ⟨64397698056191435925505171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85863597408255247900673561 64397698056191435925505171)
    ·
      refine ⟨96596547084287153888257757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64397698056191435925505171 96596547084287153888257757)
      ·
        refine ⟨36223705156607682708096659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96596547084287153888257757 36223705156607682708096659)
        ·
          refine ⟨54335557734911524062144989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36223705156607682708096659 54335557734911524062144989)
          ·
            refine ⟨20375834150591821523304371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54335557734911524062144989 20375834150591821523304371)
            ·
              refine ⟨30563751225887732284956557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20375834150591821523304371 30563751225887732284956557)
              ·
                refine ⟨11461406709707899606858709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30563751225887732284956557 11461406709707899606858709)
                ·
                  refine ⟨268626719758778897035751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11461406709707899606858709 268626719758778897035751)
                  ·
                    rfl

theorem cell22_2354169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_2354169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354169 prefixEnd_2354169 := by exact prefixLift 2354169
  have htrace : WordTrace (prefixWord ++ tailWord_2354169) baseStart_2354169 baseEnd_2354169 := by
    simpa [prefixWord, tailWord_2354169, baseEnd_2354169] using wordTrace_append hprefix tailTrace_2354169
  have hstable : (prefixWord ++ tailWord_2354169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354169).length < 2 ^ (prefixWord ++ tailWord_2354169).sum := by decide
  have hdescent : baseEnd_2354169 < baseStart_2354169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354261 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_2354261 : Nat := 118140960795 + 2354261 * 2 ^ 59
def prefixEnd_2354261 : Nat := 4983230072969 + 3 ^ 40 * 2354261 * 2
def baseEnd_2354261 : Nat := 805911652756479117806971

theorem tailTrace_2354261 : CollatzResearch.WordTrace tailWord_2354261 prefixEnd_2354261 805911652756479117806971 := by
  unfold tailWord_2354261
  simp only [CollatzResearch.WordTrace]
  refine ⟨85866952923921947613022637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57244635282614631742015091 85866952923921947613022637)
  ·
    refine ⟨32200107346470730354883489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85866952923921947613022637 32200107346470730354883489)
    ·
      refine ⟨24150080509853047766162617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32200107346470730354883489 24150080509853047766162617)
      ·
        refine ⟨18112560382389785824621963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24150080509853047766162617 18112560382389785824621963)
        ·
          refine ⟨27168840573584678736932945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18112560382389785824621963 27168840573584678736932945)
          ·
            refine ⟨20376630430188509052699709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27168840573584678736932945 20376630430188509052699709)
            ·
              refine ⟨7641236411320690894762391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20376630430188509052699709 7641236411320690894762391)
              ·
                refine ⟨11461854616981036342143587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7641236411320690894762391 11461854616981036342143587)
                ·
                  refine ⟨17192781925471554513215381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11461854616981036342143587 17192781925471554513215381)
                  ·
                    refine ⟨805911652756479117806971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17192781925471554513215381 805911652756479117806971)
                    ·
                      rfl

theorem cell22_2354261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_2354261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354261 prefixEnd_2354261 := by exact prefixLift 2354261
  have htrace : WordTrace (prefixWord ++ tailWord_2354261) baseStart_2354261 baseEnd_2354261 := by
    simpa [prefixWord, tailWord_2354261, baseEnd_2354261] using wordTrace_append hprefix tailTrace_2354261
  have hstable : (prefixWord ++ tailWord_2354261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354261).length < 2 ^ (prefixWord ++ tailWord_2354261).sum := by decide
  have hdescent : baseEnd_2354261 < baseStart_2354261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354297 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 2, 3]
def baseStart_2354297 : Nat := 118140960795 + 2354297 * 2 ^ 59
def prefixEnd_2354297 : Nat := 4983230072969 + 3 ^ 40 * 2354297 * 2
def baseEnd_2354297 : Nat := 805923976292187023906861

theorem tailTrace_2354297 : CollatzResearch.WordTrace tailWord_2354297 prefixEnd_2354297 805923976292187023906861 := by
  unfold tailWord_2354297
  simp only [CollatzResearch.WordTrace]
  refine ⟨85868265951791525761333145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57245510634527683840888763 85868265951791525761333145)
  ·
    refine ⟨64401199463843644320999859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85868265951791525761333145 64401199463843644320999859)
    ·
      refine ⟨96601799195765466481499789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64401199463843644320999859 96601799195765466481499789)
      ·
        refine ⟨36225674698412049930562421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96601799195765466481499789 36225674698412049930562421)
        ·
          refine ⟨3396157002976129680990227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36225674698412049930562421 3396157002976129680990227)
          ·
            refine ⟨5094235504464194521485341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396157002976129680990227 5094235504464194521485341)
            ·
              refine ⟨1910338314174072945557003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5094235504464194521485341 1910338314174072945557003)
              ·
                refine ⟨2865507471261109418335505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910338314174072945557003 2865507471261109418335505)
                ·
                  refine ⟨2149130603445832063751629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2865507471261109418335505 2149130603445832063751629)
                  ·
                    refine ⟨805923976292187023906861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149130603445832063751629 805923976292187023906861)
                    ·
                      rfl

theorem cell22_2354297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 2, 3].length) (baseStart_2354297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354297 prefixEnd_2354297 := by exact prefixLift 2354297
  have htrace : WordTrace (prefixWord ++ tailWord_2354297) baseStart_2354297 baseEnd_2354297 := by
    simpa [prefixWord, tailWord_2354297, baseEnd_2354297] using wordTrace_append hprefix tailTrace_2354297
  have hstable : (prefixWord ++ tailWord_2354297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354297).length < 2 ^ (prefixWord ++ tailWord_2354297).sum := by decide
  have hdescent : baseEnd_2354297 < baseStart_2354297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354325 : List Nat := [1, 3, 2, 1, 1, 1, 2, 7, 1, 3]
def baseStart_2354325 : Nat := 118140960795 + 2354325 * 2 ^ 59
def prefixEnd_2354325 : Nat := 4983230072969 + 3 ^ 40 * 2354325 * 2
def baseEnd_2354325 : Nat := 805933561264404284206775

theorem tailTrace_2354325 : CollatzResearch.WordTrace tailWord_2354325 prefixEnd_2354325 805933561264404284206775 := by
  unfold tailWord_2354325
  simp only [CollatzResearch.WordTrace]
  refine ⟨85869287195690086543352429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57246191463793391028901619 85869287195690086543352429)
  ·
    refine ⟨32200982698383782453757161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85869287195690086543352429 32200982698383782453757161)
    ·
      refine ⟨24150737023787836840317871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32200982698383782453757161 24150737023787836840317871)
      ·
        refine ⟨36226105535681755260476807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24150737023787836840317871 36226105535681755260476807)
        ·
          refine ⟨54339158303522632890715211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36226105535681755260476807 54339158303522632890715211)
          ·
            refine ⟨81508737455283949336072817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54339158303522632890715211 81508737455283949336072817)
            ·
              refine ⟨61131553091462962002054613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81508737455283949336072817 61131553091462962002054613)
              ·
                refine ⟨1432770775581163171923155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61131553091462962002054613 1432770775581163171923155)
                ·
                  refine ⟨2149156163371744757884733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1432770775581163171923155 2149156163371744757884733)
                  ·
                    refine ⟨805933561264404284206775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149156163371744757884733 805933561264404284206775)
                    ·
                      rfl

theorem cell22_2354325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_2354325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354325 prefixEnd_2354325 := by exact prefixLift 2354325
  have htrace : WordTrace (prefixWord ++ tailWord_2354325) baseStart_2354325 baseEnd_2354325 := by
    simpa [prefixWord, tailWord_2354325, baseEnd_2354325] using wordTrace_append hprefix tailTrace_2354325
  have hstable : (prefixWord ++ tailWord_2354325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354325).length < 2 ^ (prefixWord ++ tailWord_2354325).sum := by decide
  have hdescent : baseEnd_2354325 < baseStart_2354325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354400 : List Nat := [2, 1, 1, 3, 1, 5, 1, 4, 4]
def baseStart_2354400 : Nat := 118140960795 + 2354400 * 2 ^ 59
def prefixEnd_2354400 : Nat := 4983230072969 + 3 ^ 40 * 2354400 * 2
def baseEnd_2354400 : Nat := 268653078432376362860515

theorem tailTrace_2354400 : CollatzResearch.WordTrace tailWord_2354400 prefixEnd_2354400 268653078432376362860515 := by
  unfold tailWord_2354400
  simp only [CollatzResearch.WordTrace]
  refine ⟨42936011335209187176166327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57248015113612249568221769 42936011335209187176166327)
  ·
    refine ⟨64404017002813780764249491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42936011335209187176166327 64404017002813780764249491)
    ·
      refine ⟨96606025504220671146374237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64404017002813780764249491 96606025504220671146374237)
      ·
        refine ⟨36227259564082751679890339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96606025504220671146374237 36227259564082751679890339)
        ·
          refine ⟨54340889346124127519835509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36227259564082751679890339 54340889346124127519835509)
          ·
            refine ⟨5094458376199136954984579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54340889346124127519835509 5094458376199136954984579)
            ·
              refine ⟨7641687564298705432476869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5094458376199136954984579 7641687564298705432476869)
              ·
                refine ⟨1432816418306007268589413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7641687564298705432476869 1432816418306007268589413)
                ·
                  refine ⟨268653078432376362860515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432816418306007268589413 268653078432376362860515)
                  ·
                    rfl

theorem cell22_2354400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 4].length) (baseStart_2354400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354400 prefixEnd_2354400 := by exact prefixLift 2354400
  have htrace : WordTrace (prefixWord ++ tailWord_2354400) baseStart_2354400 baseEnd_2354400 := by
    simpa [prefixWord, tailWord_2354400, baseEnd_2354400] using wordTrace_append hprefix tailTrace_2354400
  have hstable : (prefixWord ++ tailWord_2354400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354400).length < 2 ^ (prefixWord ++ tailWord_2354400).sum := by decide
  have hdescent : baseEnd_2354400 < baseStart_2354400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354415 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 1, 5]
def baseStart_2354415 : Nat := 118140960795 + 2354415 * 2 ^ 59
def prefixEnd_2354415 : Nat := 4983230072969 + 3 ^ 40 * 2354415 * 2
def baseEnd_2354415 : Nat := 805964370103674049456499

theorem tailTrace_2354415 : CollatzResearch.WordTrace tailWord_2354415 prefixEnd_2354415 805964370103674049456499 := by
  unfold tailWord_2354415
  simp only [CollatzResearch.WordTrace]
  refine ⟨85872569765364031914128699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57248379843576021276085799 85872569765364031914128699)
  ·
    refine ⟨128808854648046047871193049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85872569765364031914128699 128808854648046047871193049)
    ·
      refine ⟨96606640986034535903394787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128808854648046047871193049 96606640986034535903394787)
      ·
        refine ⟨144909961479051803855092181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96606640986034535903394787 144909961479051803855092181)
        ·
          refine ⟨3396327222165276652853723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 144909961479051803855092181 3396327222165276652853723)
          ·
            refine ⟨5094490833247914979280585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396327222165276652853723 5094490833247914979280585)
            ·
              refine ⟨3820868124935936234460439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5094490833247914979280585 3820868124935936234460439)
              ·
                refine ⟨5731302187403904351690659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3820868124935936234460439 5731302187403904351690659)
                ·
                  refine ⟨8596953281105856527535989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5731302187403904351690659 8596953281105856527535989)
                  ·
                    refine ⟨805964370103674049456499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8596953281105856527535989 805964370103674049456499)
                    ·
                      rfl

theorem cell22_2354415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_2354415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354415 prefixEnd_2354415 := by exact prefixLift 2354415
  have htrace : WordTrace (prefixWord ++ tailWord_2354415) baseStart_2354415 baseEnd_2354415 := by
    simpa [prefixWord, tailWord_2354415, baseEnd_2354415] using wordTrace_append hprefix tailTrace_2354415
  have hstable : (prefixWord ++ tailWord_2354415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354415).length < 2 ^ (prefixWord ++ tailWord_2354415).sum := by decide
  have hdescent : baseEnd_2354415 < baseStart_2354415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354430 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2354430 : Nat := 118140960795 + 2354430 * 2 ^ 59
def prefixEnd_2354430 : Nat := 4983230072969 + 3 ^ 40 * 2354430 * 2
def baseEnd_2354430 : Nat := 805969504910219010331453

theorem tailTrace_2354430 : CollatzResearch.WordTrace tailWord_2354430 prefixEnd_2354430 805969504910219010331453 := by
  unfold tailWord_2354430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10734139607538711184490593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57248744573539792983949829 10734139607538711184490593)
  ·
    refine ⟨8050604705654033388367945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10734139607538711184490593 8050604705654033388367945)
    ·
      refine ⟨6037953529240525041275959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8050604705654033388367945 6037953529240525041275959)
      ·
        refine ⟨9056930293860787561913939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6037953529240525041275959 9056930293860787561913939)
        ·
          refine ⟨13585395440791181342870909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9056930293860787561913939 13585395440791181342870909)
          ·
            refine ⟨5094523290296693003576591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13585395440791181342870909 5094523290296693003576591)
            ·
              refine ⟨7641784935445039505364887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5094523290296693003576591 7641784935445039505364887)
              ·
                refine ⟨11462677403167559258047331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7641784935445039505364887 11462677403167559258047331)
                ·
                  refine ⟨17194016104751338887070997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11462677403167559258047331 17194016104751338887070997)
                  ·
                    refine ⟨805969504910219010331453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17194016104751338887070997 805969504910219010331453)
                    ·
                      rfl

theorem cell22_2354430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2354430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354430 prefixEnd_2354430 := by exact prefixLift 2354430
  have htrace : WordTrace (prefixWord ++ tailWord_2354430) baseStart_2354430 baseEnd_2354430 := by
    simpa [prefixWord, tailWord_2354430, baseEnd_2354430] using wordTrace_append hprefix tailTrace_2354430
  have hstable : (prefixWord ++ tailWord_2354430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354430).length < 2 ^ (prefixWord ++ tailWord_2354430).sum := by decide
  have hdescent : baseEnd_2354430 < baseStart_2354430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354434 : List Nat := [3, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2354434 : Nat := 118140960795 + 2354434 * 2 ^ 59
def prefixEnd_2354434 : Nat := 4983230072969 + 3 ^ 40 * 2354434 * 2
def baseEnd_2354434 : Nat := 268656958063988111077147

theorem tailTrace_2354434 : CollatzResearch.WordTrace tailWord_2354434 prefixEnd_2354434 268656958063988111077147 := by
  unfold tailWord_2354434
  simp only [CollatzResearch.WordTrace]
  refine ⟨21468315688073799539767589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57248841834863465439380237 21468315688073799539767589)
  ·
    refine ⟨4025309191513837413706423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21468315688073799539767589 4025309191513837413706423)
    ·
      refine ⟨6037963787270756120559635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4025309191513837413706423 6037963787270756120559635)
      ·
        refine ⟨9056945680906134180839453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6037963787270756120559635 9056945680906134180839453)
        ·
          refine ⟨3396354630339800317814795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9056945680906134180839453 3396354630339800317814795)
          ·
            refine ⟨5094531945509700476722193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3396354630339800317814795 5094531945509700476722193)
            ·
              refine ⟨3820898959132275357541645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5094531945509700476722193 3820898959132275357541645)
              ·
                refine ⟨1432837109674603259078117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3820898959132275357541645 1432837109674603259078117)
                ·
                  refine ⟨268656958063988111077147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1432837109674603259078117 268656958063988111077147)
                  ·
                    rfl

theorem cell22_2354434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2354434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354434 prefixEnd_2354434 := by exact prefixLift 2354434
  have htrace : WordTrace (prefixWord ++ tailWord_2354434) baseStart_2354434 baseEnd_2354434 := by
    simpa [prefixWord, tailWord_2354434, baseEnd_2354434] using wordTrace_append hprefix tailTrace_2354434
  have hstable : (prefixWord ++ tailWord_2354434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354434).length < 2 ^ (prefixWord ++ tailWord_2354434).sum := by decide
  have hdescent : baseEnd_2354434 < baseStart_2354434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354460 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_2354460 : Nat := 118140960795 + 2354460 * 2 ^ 59
def prefixEnd_2354460 : Nat := 4983230072969 + 3 ^ 40 * 2354460 * 2
def baseEnd_2354460 : Nat := 805979774523308932081361

theorem tailTrace_2354460 : CollatzResearch.WordTrace tailWord_2354460 prefixEnd_2354460 805979774523308932081361 := by
  unfold tailWord_2354460
  simp only [CollatzResearch.WordTrace]
  refine ⟨42937105525100502299758417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57249474033467336399677889 42937105525100502299758417)
  ·
    refine ⟨32202829143825376724818813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42937105525100502299758417 32202829143825376724818813)
    ·
      refine ⟨12076060928934516271807055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32202829143825376724818813 12076060928934516271807055)
      ·
        refine ⟨18114091393401774407710583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12076060928934516271807055 18114091393401774407710583)
        ·
          refine ⟨27171137090102661611565875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18114091393401774407710583 27171137090102661611565875)
          ·
            refine ⟨40756705635153992417348813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27171137090102661611565875 40756705635153992417348813)
            ·
              refine ⟨15283764613182747156505805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40756705635153992417348813 15283764613182747156505805)
              ·
                refine ⟨5731411729943530183689677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15283764613182747156505805 5731411729943530183689677)
                ·
                  refine ⟨2149279398728823818883629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5731411729943530183689677 2149279398728823818883629)
                  ·
                    refine ⟨805979774523308932081361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149279398728823818883629 805979774523308932081361)
                    ·
                      rfl

theorem cell22_2354460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_2354460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354460 prefixEnd_2354460 := by exact prefixLift 2354460
  have htrace : WordTrace (prefixWord ++ tailWord_2354460) baseStart_2354460 baseEnd_2354460 := by
    simpa [prefixWord, tailWord_2354460, baseEnd_2354460] using wordTrace_append hprefix tailTrace_2354460
  have hstable : (prefixWord ++ tailWord_2354460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354460).length < 2 ^ (prefixWord ++ tailWord_2354460).sum := by decide
  have hdescent : baseEnd_2354460 < baseStart_2354460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354563 : List Nat := [1, 1, 1, 3, 5, 11]
def baseStart_2354563 : Nat := 118140960795 + 2354563 * 2 ^ 59
def prefixEnd_2354563 : Nat := 4983230072969 + 3 ^ 40 * 2354563 * 2
def baseEnd_2354563 : Nat := 9950802883064827120445

theorem tailTrace_2354563 : CollatzResearch.WordTrace tailWord_2354563 prefixEnd_2354563 9950802883064827120445 := by
  unfold tailWord_2354563
  simp only [CollatzResearch.WordTrace]
  refine ⟨85877967768827853190516343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57251978512551902127010895 85877967768827853190516343)
  ·
    refine ⟨128816951653241779785774515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85877967768827853190516343 128816951653241779785774515)
    ·
      refine ⟨193225427479862669678661773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128816951653241779785774515 193225427479862669678661773)
      ·
        refine ⟨72459535304948501129498165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193225427479862669678661773 72459535304948501129498165)
        ·
          refine ⟨6793081434838921980890453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72459535304948501129498165 6793081434838921980890453)
          ·
            refine ⟨9950802883064827120445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6793081434838921980890453 9950802883064827120445)
            ·
              rfl

theorem cell22_2354563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 11].length) (baseStart_2354563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354563 prefixEnd_2354563 := by exact prefixLift 2354563
  have htrace : WordTrace (prefixWord ++ tailWord_2354563) baseStart_2354563 baseEnd_2354563 := by
    simpa [prefixWord, tailWord_2354563, baseEnd_2354563] using wordTrace_append hprefix tailTrace_2354563
  have hstable : (prefixWord ++ tailWord_2354563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354563).length < 2 ^ (prefixWord ++ tailWord_2354563).sum := by decide
  have hdescent : baseEnd_2354563 < baseStart_2354563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354565 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_2354565 : Nat := 118140960795 + 2354565 * 2 ^ 59
def prefixEnd_2354565 : Nat := 4983230072969 + 3 ^ 40 * 2354565 * 2
def baseEnd_2354565 : Nat := 806015718169123658206039

theorem tailTrace_2354565 : CollatzResearch.WordTrace tailWord_2354565 prefixEnd_2354565 806015718169123658206039 := by
  unfold tailWord_2354565
  simp only [CollatzResearch.WordTrace]
  refine ⟨85878040714820607532089149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57252027143213738354726099 85878040714820607532089149)
  ·
    refine ⟨32204265268057727824533431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85878040714820607532089149 32204265268057727824533431)
    ·
      refine ⟨48306397902086591736800147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32204265268057727824533431 48306397902086591736800147)
      ·
        refine ⟨72459596853129887605200221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48306397902086591736800147 72459596853129887605200221)
        ·
          refine ⟨27172348819923707851950083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72459596853129887605200221 27172348819923707851950083)
          ·
            refine ⟨40758523229885561777925125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27172348819923707851950083 40758523229885561777925125)
            ·
              refine ⟨7642223105603542833360961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40758523229885561777925125 7642223105603542833360961)
              ·
                refine ⟨5731667329202657125020721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7642223105603542833360961 5731667329202657125020721)
                ·
                  refine ⟨4298750496901992843765541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5731667329202657125020721 4298750496901992843765541)
                  ·
                    refine ⟨806015718169123658206039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4298750496901992843765541 806015718169123658206039)
                    ·
                      rfl

theorem cell22_2354565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_2354565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354565 prefixEnd_2354565 := by exact prefixLift 2354565
  have htrace : WordTrace (prefixWord ++ tailWord_2354565) baseStart_2354565 baseEnd_2354565 := by
    simpa [prefixWord, tailWord_2354565, baseEnd_2354565] using wordTrace_append hprefix tailTrace_2354565
  have hstable : (prefixWord ++ tailWord_2354565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354565).length < 2 ^ (prefixWord ++ tailWord_2354565).sum := by decide
  have hdescent : baseEnd_2354565 < baseStart_2354565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354567 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 2, 3]
def baseStart_2354567 : Nat := 118140960795 + 2354567 * 2 ^ 59
def prefixEnd_2354567 : Nat := 4983230072969 + 3 ^ 40 * 2354567 * 2
def baseEnd_2354567 : Nat := 806016402809996319656033

theorem tailTrace_2354567 : CollatzResearch.WordTrace tailWord_2354567 prefixEnd_2354567 806016402809996319656033 := by
  unfold tailWord_2354567
  simp only [CollatzResearch.WordTrace]
  refine ⟨85878113660813361873661955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57252075773875574582441303 85878113660813361873661955)
  ·
    refine ⟨128817170491220042810492933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85878113660813361873661955 128817170491220042810492933)
    ·
      refine ⟨24153219467103758026967425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128817170491220042810492933 24153219467103758026967425)
      ·
        refine ⟨18114914600327818520225569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24153219467103758026967425 18114914600327818520225569)
        ·
          refine ⟨13586185950245863890169177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18114914600327818520225569 13586185950245863890169177)
          ·
            refine ⟨10189639462684397917626883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13586185950245863890169177 10189639462684397917626883)
            ·
              refine ⟨15284459194026596876440325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10189639462684397917626883 15284459194026596876440325)
              ·
                refine ⟨2865836098879986914332561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15284459194026596876440325 2865836098879986914332561)
                ·
                  refine ⟨2149377074159990185749421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2865836098879986914332561 2149377074159990185749421)
                  ·
                    refine ⟨806016402809996319656033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149377074159990185749421 806016402809996319656033)
                    ·
                      rfl

theorem cell22_2354567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_2354567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354567 prefixEnd_2354567 := by exact prefixLift 2354567
  have htrace : WordTrace (prefixWord ++ tailWord_2354567) baseStart_2354567 baseEnd_2354567 := by
    simpa [prefixWord, tailWord_2354567, baseEnd_2354567] using wordTrace_append hprefix tailTrace_2354567
  have hstable : (prefixWord ++ tailWord_2354567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354567).length < 2 ^ (prefixWord ++ tailWord_2354567).sum := by decide
  have hdescent : baseEnd_2354567 < baseStart_2354567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354672 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_2354672 : Nat := 118140960795 + 2354672 * 2 ^ 59
def prefixEnd_2354672 : Nat := 4983230072969 + 3 ^ 40 * 2354672 * 2
def baseEnd_2354672 : Nat := 806052346455811045780711

theorem tailTrace_2354672 : CollatzResearch.WordTrace tailWord_2354672 prefixEnd_2354672 806052346455811045780711 := by
  unfold tailWord_2354672
  simp only [CollatzResearch.WordTrace]
  refine ⟨42940971662716482403117135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57254628883621976537489513 42940971662716482403117135)
  ·
    refine ⟨64411457494074723604675703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42940971662716482403117135 64411457494074723604675703)
    ·
      refine ⟨96617186241112085407013555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64411457494074723604675703 96617186241112085407013555)
      ·
        refine ⟨144925779361668128110520333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96617186241112085407013555 144925779361668128110520333)
        ·
          refine ⟨54347167260625548041445125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144925779361668128110520333 54347167260625548041445125)
          ·
            refine ⟨10190093861367290257770961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54347167260625548041445125 10190093861367290257770961)
            ·
              refine ⟨7642570396025467693328221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10190093861367290257770961 7642570396025467693328221)
              ·
                refine ⟨2865963898509550384998083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7642570396025467693328221 2865963898509550384998083)
                ·
                  refine ⟨4298945847764325577497125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865963898509550384998083 4298945847764325577497125)
                  ·
                    refine ⟨806052346455811045780711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4298945847764325577497125 806052346455811045780711)
                    ·
                      rfl

theorem cell22_2354672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_2354672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354672 prefixEnd_2354672 := by exact prefixLift 2354672
  have htrace : WordTrace (prefixWord ++ tailWord_2354672) baseStart_2354672 baseEnd_2354672 := by
    simpa [prefixWord, tailWord_2354672, baseEnd_2354672] using wordTrace_append hprefix tailTrace_2354672
  have hstable : (prefixWord ++ tailWord_2354672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354672).length < 2 ^ (prefixWord ++ tailWord_2354672).sum := by decide
  have hdescent : baseEnd_2354672 < baseStart_2354672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354734 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2354734 : Nat := 118140960795 + 2354734 * 2 ^ 59
def prefixEnd_2354734 : Nat := 4983230072969 + 3 ^ 40 * 2354734 * 2
def baseEnd_2354734 : Nat := 806073570322863550730521

theorem tailTrace_2354734 : CollatzResearch.WordTrace tailWord_2354734 prefixEnd_2354734 806073570322863550730521 := by
  unfold tailWord_2354734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10735525581401043674373907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57256136434138899596660837 10735525581401043674373907)
  ·
    refine ⟨16103288372101565511560861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10735525581401043674373907 16103288372101565511560861)
    ·
      refine ⟨6038733139538087066835323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16103288372101565511560861 6038733139538087066835323)
      ·
        refine ⟨9058099709307130600252985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6038733139538087066835323 9058099709307130600252985)
        ·
          refine ⟨6793574781980347950189739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9058099709307130600252985 6793574781980347950189739)
          ·
            refine ⟨10190362172970521925284609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6793574781980347950189739 10190362172970521925284609)
            ·
              refine ⟨7642771629727891443963457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10190362172970521925284609 7642771629727891443963457)
              ·
                refine ⟨5732078722295918582972593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7642771629727891443963457 5732078722295918582972593)
                ·
                  refine ⟨4299059041721938937229445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5732078722295918582972593 4299059041721938937229445)
                  ·
                    refine ⟨806073570322863550730521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4299059041721938937229445 806073570322863550730521)
                    ·
                      rfl

theorem cell22_2354734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2354734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354734 prefixEnd_2354734 := by exact prefixLift 2354734
  have htrace : WordTrace (prefixWord ++ tailWord_2354734) baseStart_2354734 baseEnd_2354734 := by
    simpa [prefixWord, tailWord_2354734, baseEnd_2354734] using wordTrace_append hprefix tailTrace_2354734
  have hstable : (prefixWord ++ tailWord_2354734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354734).length < 2 ^ (prefixWord ++ tailWord_2354734).sum := by decide
  have hdescent : baseEnd_2354734 < baseStart_2354734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354749 : List Nat := [1, 4, 1, 3, 3, 2, 1, 7]
def baseStart_2354749 : Nat := 118140960795 + 2354749 * 2 ^ 59
def prefixEnd_2354749 : Nat := 4983230072969 + 3 ^ 40 * 2354749 * 2
def baseEnd_2354749 : Nat := 89564300569934279067275

theorem tailTrace_2354749 : CollatzResearch.WordTrace tailWord_2354749 prefixEnd_2354749 89564300569934279067275 := by
  unfold tailWord_2354749
  simp only [CollatzResearch.WordTrace]
  refine ⟨85884751746154006956787301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57256501164102671304524867 85884751746154006956787301)
  ·
    refine ⟨16103390952403876304397619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85884751746154006956787301 16103390952403876304397619)
    ·
      refine ⟨24155086428605814456596429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16103390952403876304397619 24155086428605814456596429)
      ·
        refine ⟨9058157410727180421223661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24155086428605814456596429 9058157410727180421223661)
        ·
          refine ⟨3396809029022692657958873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9058157410727180421223661 3396809029022692657958873)
          ·
            refine ⟨2547606771767019493469155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3396809029022692657958873 2547606771767019493469155)
            ·
              refine ⟨3821410157650529240203733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2547606771767019493469155 3821410157650529240203733)
              ·
                refine ⟨89564300569934279067275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3821410157650529240203733 89564300569934279067275)
                ·
                  rfl

theorem cell22_2354749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 7].length) (baseStart_2354749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354749 prefixEnd_2354749 := by exact prefixLift 2354749
  have htrace : WordTrace (prefixWord ++ tailWord_2354749) baseStart_2354749 baseEnd_2354749 := by
    simpa [prefixWord, tailWord_2354749, baseEnd_2354749] using wordTrace_append hprefix tailTrace_2354749
  have hstable : (prefixWord ++ tailWord_2354749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354749).length < 2 ^ (prefixWord ++ tailWord_2354749).sum := by decide
  have hdescent : baseEnd_2354749 < baseStart_2354749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
