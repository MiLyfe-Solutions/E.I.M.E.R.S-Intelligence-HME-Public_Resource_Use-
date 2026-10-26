import V185TrunkScan23Chunk0618

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3660042 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3660042 : Nat := 118140960795 + 3660042 * 2 ^ 59
def prefixEnd_3660042 : Nat := 4983230072969 + 3 ^ 40 * 3660042 * 2
def baseEnd_3660042 : Nat := 1879360761643274302542779

theorem tailTrace_3660042 : CollatzResearch.WordTrace tailWord_3660042 prefixEnd_3660042 1879360761643274302542779 := by
  unfold tailWord_3660042
  simp only [CollatzResearch.WordTrace]
  refine ⟨33373174651575098563279595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88995132404200262835412253 33373174651575098563279595)
  ·
    refine ⟨50059761977362647844919393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33373174651575098563279595 50059761977362647844919393)
    ·
      refine ⟨37544821483021985883689545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50059761977362647844919393 37544821483021985883689545)
      ·
        refine ⟨28158616112266489412767159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37544821483021985883689545 28158616112266489412767159)
        ·
          refine ⟨42237924168399734119150739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28158616112266489412767159 42237924168399734119150739)
          ·
            refine ⟨63356886252599601178726109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42237924168399734119150739 63356886252599601178726109)
            ·
              refine ⟨23758832344724850442022291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63356886252599601178726109 23758832344724850442022291)
              ·
                refine ⟨35638248517087275663033437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23758832344724850442022291 35638248517087275663033437)
                ·
                  refine ⟨13364343193907728373637539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35638248517087275663033437 13364343193907728373637539)
                  ·
                    refine ⟨20046514790861592560456309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13364343193907728373637539 20046514790861592560456309)
                    ·
                      refine ⟨1879360761643274302542779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20046514790861592560456309 1879360761643274302542779)
                      ·
                        rfl

theorem cell23_3660042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3660042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660042 prefixEnd_3660042 := by exact prefixLift 3660042
  have htrace : WordTrace (prefixWord ++ tailWord_3660042) baseStart_3660042 baseEnd_3660042 := by
    simpa [prefixWord, tailWord_3660042, baseEnd_3660042] using wordTrace_append hprefix tailTrace_3660042
  have hstable : (prefixWord ++ tailWord_3660042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660042).length < 2 ^ (prefixWord ++ tailWord_3660042).sum := by decide
  have hdescent : baseEnd_3660042 < baseStart_3660042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660049 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 1, 6]
def baseStart_3660049 : Nat := 118140960795 + 3660049 * 2 ^ 59
def prefixEnd_3660049 : Nat := 4983230072969 + 3 ^ 40 * 3660049 * 2
def baseEnd_3660049 : Nat := 626454785335951925051749

theorem tailTrace_3660049 : CollatzResearch.WordTrace tailWord_3660049 prefixEnd_3660049 626454785335951925051749 := by
  unfold tailWord_3660049
  simp only [CollatzResearch.WordTrace]
  refine ⟨133492953917275034448623201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88995302611516689632415467 133492953917275034448623201)
  ·
    refine ⟨100119715437956275836467401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133492953917275034448623201 100119715437956275836467401)
    ·
      refine ⟨75089786578467206877350551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100119715437956275836467401 75089786578467206877350551)
      ·
        refine ⟨112634679867700810316025827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75089786578467206877350551 112634679867700810316025827)
        ·
          refine ⟨168952019801551215474038741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112634679867700810316025827 168952019801551215474038741)
          ·
            refine ⟨3959812964098856612672783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168952019801551215474038741 3959812964098856612672783)
            ·
              refine ⟨5939719446148284919009175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959812964098856612672783 5939719446148284919009175)
              ·
                refine ⟨8909579169222427378513763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939719446148284919009175 8909579169222427378513763)
                ·
                  refine ⟨13364368753833641067770645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8909579169222427378513763 13364368753833641067770645)
                  ·
                    refine ⟨626454785335951925051749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13364368753833641067770645 626454785335951925051749)
                    ·
                      rfl

theorem cell23_3660049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_3660049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660049 prefixEnd_3660049 := by exact prefixLift 3660049
  have htrace : WordTrace (prefixWord ++ tailWord_3660049) baseStart_3660049 baseEnd_3660049 := by
    simpa [prefixWord, tailWord_3660049, baseEnd_3660049] using wordTrace_append hprefix tailTrace_3660049
  have hstable : (prefixWord ++ tailWord_3660049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660049).length < 2 ^ (prefixWord ++ tailWord_3660049).sum := by decide
  have hdescent : baseEnd_3660049 < baseStart_3660049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660056 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 3, 2, 2]
def baseStart_3660056 : Nat := 118140960795 + 3660056 * 2 ^ 59
def prefixEnd_3660056 : Nat := 4983230072969 + 3 ^ 40 * 3660056 * 2
def baseEnd_3660056 : Nat := 1879367950372437247767715

theorem tailTrace_3660056 : CollatzResearch.WordTrace tailWord_3660056 prefixEnd_3660056 1879367950372437247767715 := by
  unfold tailWord_3660056
  simp only [CollatzResearch.WordTrace]
  refine ⟨66746604614124837322064011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88995472818833116429418681 66746604614124837322064011)
  ·
    refine ⟨100119906921187255983096017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66746604614124837322064011 100119906921187255983096017)
    ·
      refine ⟨75089930190890441987322013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100119906921187255983096017 75089930190890441987322013)
      ·
        refine ⟨28158723821583915745245755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75089930190890441987322013 28158723821583915745245755)
        ·
          refine ⟨42238085732375873617868633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28158723821583915745245755 42238085732375873617868633)
          ·
            refine ⟨31678564299281905213401475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42238085732375873617868633 31678564299281905213401475)
            ·
              refine ⟨47517846448922857820102213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31678564299281905213401475 47517846448922857820102213)
              ·
                refine ⟨8909596209173035841269165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47517846448922857820102213 8909596209173035841269165)
                ·
                  refine ⟨3341098578439888440475937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8909596209173035841269165 3341098578439888440475937)
                  ·
                    refine ⟨2505823933829916330356953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3341098578439888440475937 2505823933829916330356953)
                    ·
                      refine ⟨1879367950372437247767715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2505823933829916330356953 1879367950372437247767715)
                      ·
                        rfl

theorem cell23_3660056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_3660056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660056 prefixEnd_3660056 := by exact prefixLift 3660056
  have htrace : WordTrace (prefixWord ++ tailWord_3660056) baseStart_3660056 baseEnd_3660056 := by
    simpa [prefixWord, tailWord_3660056, baseEnd_3660056] using wordTrace_append hprefix tailTrace_3660056
  have hstable : (prefixWord ++ tailWord_3660056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660056).length < 2 ^ (prefixWord ++ tailWord_3660056).sum := by decide
  have hdescent : baseEnd_3660056 < baseStart_3660056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660059 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 3]
def baseStart_3660059 : Nat := 118140960795 + 3660059 * 2 ^ 59
def prefixEnd_3660059 : Nat := 4983230072969 + 3 ^ 40 * 3660059 * 2
def baseEnd_3660059 : Nat := 1879369490814400736030201

theorem tailTrace_3660059 : CollatzResearch.WordTrace tailWord_3660059 prefixEnd_3660059 1879369490814400736030201 := by
  unfold tailWord_3660059
  simp only [CollatzResearch.WordTrace]
  refine ⟨133493318647238806156487231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88995545764825870770991487 133493318647238806156487231)
  ·
    refine ⟨200239977970858209234730847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133493318647238806156487231 200239977970858209234730847)
    ·
      refine ⟨300359966956287313852096271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200239977970858209234730847 300359966956287313852096271)
      ·
        refine ⟨450539950434430970778144407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300359966956287313852096271 450539950434430970778144407)
        ·
          refine ⟨675809925651646456167216611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450539950434430970778144407 675809925651646456167216611)
          ·
            refine ⟨1013714888477469684250824917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675809925651646456167216611 1013714888477469684250824917)
            ·
              refine ⟨23758942698690695724628709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1013714888477469684250824917 23758942698690695724628709)
              ·
                refine ⟨4454801756004505448367883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23758942698690695724628709 4454801756004505448367883)
                ·
                  refine ⟨6682202634006758172551825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454801756004505448367883 6682202634006758172551825)
                  ·
                    refine ⟨5011651975505068629413869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6682202634006758172551825 5011651975505068629413869)
                    ·
                      refine ⟨1879369490814400736030201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5011651975505068629413869 1879369490814400736030201)
                      ·
                        rfl

theorem cell23_3660059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 3].length) (baseStart_3660059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660059 prefixEnd_3660059 := by exact prefixLift 3660059
  have htrace : WordTrace (prefixWord ++ tailWord_3660059) baseStart_3660059 baseEnd_3660059 := by
    simpa [prefixWord, tailWord_3660059, baseEnd_3660059] using wordTrace_append hprefix tailTrace_3660059
  have hstable : (prefixWord ++ tailWord_3660059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660059).length < 2 ^ (prefixWord ++ tailWord_3660059).sum := by decide
  have hdescent : baseEnd_3660059 < baseStart_3660059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660092 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_3660092 : Nat := 118140960795 + 3660092 * 2 ^ 59
def prefixEnd_3660092 : Nat := 4983230072969 + 3 ^ 40 * 3660092 * 2
def baseEnd_3660092 : Nat := 626462145225333035639183

theorem tailTrace_3660092 : CollatzResearch.WordTrace tailWord_3660092 prefixEnd_3660092 626462145225333035639183 := by
  unfold tailWord_3660092
  simp only [CollatzResearch.WordTrace]
  refine ⟨66747261128059626396219265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88996348170746168528292353 66747261128059626396219265)
  ·
    refine ⟨50060445846044719797164449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66747261128059626396219265 50060445846044719797164449)
    ·
      refine ⟨37545334384533539847873337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50060445846044719797164449 37545334384533539847873337)
      ·
        refine ⟨28159000788400154885905003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37545334384533539847873337 28159000788400154885905003)
        ·
          refine ⟨42238501182600232328857505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28159000788400154885905003 42238501182600232328857505)
          ·
            refine ⟨31678875886950174246643129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42238501182600232328857505 31678875886950174246643129)
            ·
              refine ⟨23759156915212630684982347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31678875886950174246643129 23759156915212630684982347)
              ·
                refine ⟨35638735372818946027473521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23759156915212630684982347 35638735372818946027473521)
                ·
                  refine ⟨26729051529614209520605141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35638735372818946027473521 26729051529614209520605141)
                  ·
                    refine ⟨626462145225333035639183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26729051529614209520605141 626462145225333035639183)
                    ·
                      rfl

theorem cell23_3660092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_3660092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660092 prefixEnd_3660092 := by exact prefixLift 3660092
  have htrace : WordTrace (prefixWord ++ tailWord_3660092) baseStart_3660092 baseEnd_3660092 := by
    simpa [prefixWord, tailWord_3660092, baseEnd_3660092] using wordTrace_append hprefix tailTrace_3660092
  have hstable : (prefixWord ++ tailWord_3660092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660092).length < 2 ^ (prefixWord ++ tailWord_3660092).sum := by decide
  have hdescent : baseEnd_3660092 < baseStart_3660092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660122 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_3660122 : Nat := 118140960795 + 3660122 * 2 ^ 59
def prefixEnd_3660122 : Nat := 4983230072969 + 3 ^ 40 * 3660122 * 2
def baseEnd_3660122 : Nat := 626467280031877996514137

theorem tailTrace_3660122 : CollatzResearch.WordTrace tailWord_3660122 prefixEnd_3660122 626467280031877996514137 := by
  unfold tailWord_3660122
  simp only [CollatzResearch.WordTrace]
  refine ⟨33373904111502641979007655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88997077630673711944020413 33373904111502641979007655)
  ·
    refine ⟨50060856167253962968511483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33373904111502641979007655 50060856167253962968511483)
    ·
      refine ⟨75091284250880944452767225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50060856167253962968511483 75091284250880944452767225)
      ·
        refine ⟨56318463188160708339575419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75091284250880944452767225 56318463188160708339575419)
        ·
          refine ⟨84477694782241062509363129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56318463188160708339575419 84477694782241062509363129)
          ·
            refine ⟨63358271086680796882022347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84477694782241062509363129 63358271086680796882022347)
            ·
              refine ⟨95037406630021195323033521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63358271086680796882022347 95037406630021195323033521)
              ·
                refine ⟨71278054972515896492275141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95037406630021195323033521 71278054972515896492275141)
                ·
                  refine ⟨13364635307346730592301589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71278054972515896492275141 13364635307346730592301589)
                  ·
                    refine ⟨626467280031877996514137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13364635307346730592301589 626467280031877996514137)
                    ·
                      rfl

theorem cell23_3660122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_3660122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660122 prefixEnd_3660122 := by exact prefixLift 3660122
  have htrace : WordTrace (prefixWord ++ tailWord_3660122) baseStart_3660122 baseEnd_3660122 := by
    simpa [prefixWord, tailWord_3660122, baseEnd_3660122] using wordTrace_append hprefix tailTrace_3660122
  have hstable : (prefixWord ++ tailWord_3660122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660122).length < 2 ^ (prefixWord ++ tailWord_3660122).sum := by decide
  have hdescent : baseEnd_3660122 < baseStart_3660122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660163 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 1, 4, 2]
def baseStart_3660163 : Nat := 118140960795 + 3660163 * 2 ^ 59
def prefixEnd_3660163 : Nat := 4983230072969 + 3 ^ 40 * 3660163 * 2
def baseEnd_3660163 : Nat := 1879422892802468329129723

theorem tailTrace_3660163 : CollatzResearch.WordTrace tailWord_3660163 prefixEnd_3660163 1879422892802468329129723 := by
  unfold tailWord_3660163
  simp only [CollatzResearch.WordTrace]
  refine ⟨133497111838862031918273143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88998074559241354612182095 133497111838862031918273143)
  ·
    refine ⟨200245667758293047877409715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133497111838862031918273143 200245667758293047877409715)
    ·
      refine ⟨300368501637439571816114573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200245667758293047877409715 300368501637439571816114573)
      ·
        refine ⟨112638188114039839431042965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300368501637439571816114573 112638188114039839431042965)
        ·
          refine ⟨5279915067845617473330139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112638188114039839431042965 5279915067845617473330139)
          ·
            refine ⟨7919872601768426209995209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279915067845617473330139 7919872601768426209995209)
            ·
              refine ⟨5939904451326319657496407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7919872601768426209995209 5939904451326319657496407)
              ·
                refine ⟨8909856676989479486244611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939904451326319657496407 8909856676989479486244611)
                ·
                  refine ⟨13364785015484219229366917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8909856676989479486244611 13364785015484219229366917)
                  ·
                    refine ⟨2505897190403291105506297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13364785015484219229366917 2505897190403291105506297)
                    ·
                      refine ⟨1879422892802468329129723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2505897190403291105506297 1879422892802468329129723)
                      ·
                        rfl

theorem cell23_3660163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_3660163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660163 prefixEnd_3660163 := by exact prefixLift 3660163
  have htrace : WordTrace (prefixWord ++ tailWord_3660163) baseStart_3660163 baseEnd_3660163 := by
    simpa [prefixWord, tailWord_3660163, baseEnd_3660163] using wordTrace_append hprefix tailTrace_3660163
  have hstable : (prefixWord ++ tailWord_3660163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660163).length < 2 ^ (prefixWord ++ tailWord_3660163).sum := by decide
  have hdescent : baseEnd_3660163 < baseStart_3660163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660169 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 7]
def baseStart_3660169 : Nat := 118140960795 + 3660169 * 2 ^ 59
def prefixEnd_3660169 : Nat := 4983230072969 + 3 ^ 40 * 3660169 * 2
def baseEnd_3660169 : Nat := 208825108187377256183855

theorem tailTrace_3660169 : CollatzResearch.WordTrace tailWord_3660169 prefixEnd_3660169 208825108187377256183855 := by
  unfold tailWord_3660169
  simp only [CollatzResearch.WordTrace]
  refine ⟨133497330676840294942991561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88998220451226863295327707 133497330676840294942991561)
  ·
    refine ⟨100122998007630221207243671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133497330676840294942991561 100122998007630221207243671)
    ·
      refine ⟨150184497011445331810865507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100122998007630221207243671 150184497011445331810865507)
      ·
        refine ⟨225276745517167997716298261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150184497011445331810865507 225276745517167997716298261)
        ·
          refine ⟨10559847446117249892951481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225276745517167997716298261 10559847446117249892951481)
          ·
            refine ⟨7919885584587937419713611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10559847446117249892951481 7919885584587937419713611)
            ·
              refine ⟨11879828376881906129570417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7919885584587937419713611 11879828376881906129570417)
              ·
                refine ⟨8909871282661429597177813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11879828376881906129570417 8909871282661429597177813)
                ·
                  refine ⟨208825108187377256183855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8909871282661429597177813 208825108187377256183855)
                  ·
                    rfl

theorem cell23_3660169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 7].length) (baseStart_3660169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660169 prefixEnd_3660169 := by exact prefixLift 3660169
  have htrace : WordTrace (prefixWord ++ tailWord_3660169) baseStart_3660169 baseEnd_3660169 := by
    simpa [prefixWord, tailWord_3660169, baseEnd_3660169] using wordTrace_append hprefix tailTrace_3660169
  have hstable : (prefixWord ++ tailWord_3660169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660169).length < 2 ^ (prefixWord ++ tailWord_3660169).sum := by decide
  have hdescent : baseEnd_3660169 < baseStart_3660169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660186 : List Nat := [3, 1, 1, 4, 1, 2, 1, 5, 5]
def baseStart_3660186 : Nat := 118140960795 + 3660186 * 2 ^ 59
def prefixEnd_3660186 : Nat := 4983230072969 + 3 ^ 40 * 3660186 * 2
def baseEnd_3660186 : Nat := 208826078095280193238013

theorem tailTrace_3660186 : CollatzResearch.WordTrace tailWord_3660186 prefixEnd_3660186 208826078095280193238013 := by
  unfold tailWord_3660186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33374487679444676711590103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88998633811852471230906941 33374487679444676711590103)
  ·
    refine ⟨50061731519167015067385155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33374487679444676711590103 50061731519167015067385155)
    ·
      refine ⟨75092597278750522601077733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50061731519167015067385155 75092597278750522601077733)
      ·
        refine ⟨14079861989765722987702075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75092597278750522601077733 14079861989765722987702075)
        ·
          refine ⟨21119792984648584481553113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14079861989765722987702075 21119792984648584481553113)
          ·
            refine ⟨15839844738486438361164835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21119792984648584481553113 15839844738486438361164835)
            ·
              refine ⟨23759767107729657541747253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15839844738486438361164835 23759767107729657541747253)
              ·
                refine ⟨2227478166349655394538805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23759767107729657541747253 2227478166349655394538805)
                ·
                  refine ⟨208826078095280193238013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227478166349655394538805 208826078095280193238013)
                  ·
                    rfl

theorem cell23_3660186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_3660186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660186 prefixEnd_3660186 := by exact prefixLift 3660186
  have htrace : WordTrace (prefixWord ++ tailWord_3660186) baseStart_3660186 baseEnd_3660186 := by
    simpa [prefixWord, tailWord_3660186, baseEnd_3660186] using wordTrace_append hprefix tailTrace_3660186
  have hstable : (prefixWord ++ tailWord_3660186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660186).length < 2 ^ (prefixWord ++ tailWord_3660186).sum := by decide
  have hdescent : baseEnd_3660186 < baseStart_3660186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660256 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 3]
def baseStart_3660256 : Nat := 118140960795 + 3660256 * 2 ^ 59
def prefixEnd_3660256 : Nat := 4983230072969 + 3 ^ 40 * 3660256 * 2
def baseEnd_3660256 : Nat := 1879470646503336465266795

theorem tailTrace_3660256 : CollatzResearch.WordTrace tailWord_3660256 prefixEnd_3660256 1879470646503336465266795 := by
  unfold tailWord_3660256
  simp only [CollatzResearch.WordTrace]
  refine ⟨66750251913762554400704311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89000335885016739200939081 66750251913762554400704311)
  ·
    refine ⟨100125377870643831601056467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66750251913762554400704311 100125377870643831601056467)
    ·
      refine ⟨150188066805965747401584701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100125377870643831601056467 150188066805965747401584701)
      ·
        refine ⟨56320525052237155275594263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150188066805965747401584701 56320525052237155275594263)
        ·
          refine ⟨84480787578355732913391395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56320525052237155275594263 84480787578355732913391395)
          ·
            refine ⟨126721181367533599370087093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84480787578355732913391395 126721181367533599370087093)
            ·
              refine ⟨11880110753206274940945665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126721181367533599370087093 11880110753206274940945665)
              ·
                refine ⟨8910083064904706205709249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11880110753206274940945665 8910083064904706205709249)
                ·
                  refine ⟨6682562298678529654281937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8910083064904706205709249 6682562298678529654281937)
                  ·
                    refine ⟨5011921724008897240711453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6682562298678529654281937 5011921724008897240711453)
                    ·
                      refine ⟨1879470646503336465266795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5011921724008897240711453 1879470646503336465266795)
                      ·
                        rfl

theorem cell23_3660256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_3660256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660256 prefixEnd_3660256 := by exact prefixLift 3660256
  have htrace : WordTrace (prefixWord ++ tailWord_3660256) baseStart_3660256 baseEnd_3660256 := by
    simpa [prefixWord, tailWord_3660256, baseEnd_3660256] using wordTrace_append hprefix tailTrace_3660256
  have hstable : (prefixWord ++ tailWord_3660256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660256).length < 2 ^ (prefixWord ++ tailWord_3660256).sum := by decide
  have hdescent : baseEnd_3660256 < baseStart_3660256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660319 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 5, 6]
def baseStart_3660319 : Nat := 118140960795 + 3660319 * 2 ^ 59
def prefixEnd_3660319 : Nat := 4983230072969 + 3 ^ 40 * 3660319 * 2
def baseEnd_3660319 : Nat := 626500998594856572926335

theorem tailTrace_3660319 : CollatzResearch.WordTrace tailWord_3660319 prefixEnd_3660319 626500998594856572926335 := by
  unfold tailWord_3660319
  simp only [CollatzResearch.WordTrace]
  refine ⟨133502801626296870560952011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89001867750864580373968007 133502801626296870560952011)
  ·
    refine ⟨200254202439445305841428017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133502801626296870560952011 200254202439445305841428017)
    ·
      refine ⟨150190651829583979381071013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200254202439445305841428017 150190651829583979381071013)
      ·
        refine ⟨28160747218046996133950815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150190651829583979381071013 28160747218046996133950815)
        ·
          refine ⟨42241120827070494200926223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28160747218046996133950815 42241120827070494200926223)
          ·
            refine ⟨63361681240605741301389335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42241120827070494200926223 63361681240605741301389335)
            ·
              refine ⟨95042521860908611952084003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63361681240605741301389335 95042521860908611952084003)
              ·
                refine ⟨142563782791362917928126005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95042521860908611952084003 142563782791362917928126005)
                ·
                  refine ⟨13365354636690273555761813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142563782791362917928126005 13365354636690273555761813)
                  ·
                    refine ⟨626500998594856572926335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13365354636690273555761813 626500998594856572926335)
                    ·
                      rfl

theorem cell23_3660319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_3660319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660319 prefixEnd_3660319 := by exact prefixLift 3660319
  have htrace : WordTrace (prefixWord ++ tailWord_3660319) baseStart_3660319 baseEnd_3660319 := by
    simpa [prefixWord, tailWord_3660319, baseEnd_3660319] using wordTrace_append hprefix tailTrace_3660319
  have hstable : (prefixWord ++ tailWord_3660319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660319).length < 2 ^ (prefixWord ++ tailWord_3660319).sum := by decide
  have hdescent : baseEnd_3660319 < baseStart_3660319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660376 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_3660376 : Nat := 118140960795 + 3660376 * 2 ^ 59
def prefixEnd_3660376 : Nat := 4983230072969 + 3 ^ 40 * 3660376 * 2
def baseEnd_3660376 : Nat := 1879532264181875995766243

theorem tailTrace_3660376 : CollatzResearch.WordTrace tailWord_3660376 prefixEnd_3660376 1879532264181875995766243 := by
  unfold tailWord_3660376
  simp only [CollatzResearch.WordTrace]
  refine ⟨66752440293545184647888491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89003253724726912863851321 66752440293545184647888491)
  ·
    refine ⟨100128660440317776971832737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66752440293545184647888491 100128660440317776971832737)
    ·
      refine ⟨75096495330238332728874553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100128660440317776971832737 75096495330238332728874553)
      ·
        refine ⟨56322371497678749546655915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75096495330238332728874553 56322371497678749546655915)
        ·
          refine ⟨84483557246518124319983873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56322371497678749546655915 84483557246518124319983873)
          ·
            refine ⟨63362667934888593239987905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84483557246518124319983873 63362667934888593239987905)
            ·
              refine ⟨47522000951166444929990929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63362667934888593239987905 47522000951166444929990929)
              ·
                refine ⟨35641500713374833697493197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47522000951166444929990929 35641500713374833697493197)
                ·
                  refine ⟨13365562767515562636559949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35641500713374833697493197 13365562767515562636559949)
                  ·
                    refine ⟨5012086037818335988709981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13365562767515562636559949 5012086037818335988709981)
                    ·
                      refine ⟨1879532264181875995766243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5012086037818335988709981 1879532264181875995766243)
                      ·
                        rfl

theorem cell23_3660376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_3660376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660376 prefixEnd_3660376 := by exact prefixLift 3660376
  have htrace : WordTrace (prefixWord ++ tailWord_3660376) baseStart_3660376 baseEnd_3660376 := by
    simpa [prefixWord, tailWord_3660376, baseEnd_3660376] using wordTrace_append hprefix tailTrace_3660376
  have hstable : (prefixWord ++ tailWord_3660376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660376).length < 2 ^ (prefixWord ++ tailWord_3660376).sum := by decide
  have hdescent : baseEnd_3660376 < baseStart_3660376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660400 : List Nat := [2, 1, 1, 1, 8, 1, 2, 7]
def baseStart_3660400 : Nat := 118140960795 + 3660400 * 2 ^ 59
def prefixEnd_3660400 : Nat := 4983230072969 + 3 ^ 40 * 3660400 * 2
def baseEnd_3660400 : Nat := 69612762508058663032079

theorem tailTrace_3660400 : CollatzResearch.WordTrace tailWord_3660400 prefixEnd_3660400 69612762508058663032079 := by
  unfold tailWord_3660400
  simp only [CollatzResearch.WordTrace]
  refine ⟨66752877969501710697325327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89003837292668947596433769 66752877969501710697325327)
  ·
    refine ⟨100129316954252566045987991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66752877969501710697325327 100129316954252566045987991)
    ·
      refine ⟨150193975431378849068981987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100129316954252566045987991 150193975431378849068981987)
      ·
        refine ⟨225290963147068273603472981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150193975431378849068981987 225290963147068273603472981)
        ·
          refine ⟨2640128474379706331290699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 225290963147068273603472981 2640128474379706331290699)
          ·
            refine ⟨3960192711569559496936049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640128474379706331290699 3960192711569559496936049)
            ·
              refine ⟨2970144533677169622702037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960192711569559496936049 2970144533677169622702037)
              ·
                refine ⟨69612762508058663032079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2970144533677169622702037 69612762508058663032079)
                ·
                  rfl

theorem cell23_3660400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 7].length) (baseStart_3660400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660400 prefixEnd_3660400 := by exact prefixLift 3660400
  have htrace : WordTrace (prefixWord ++ tailWord_3660400) baseStart_3660400 baseEnd_3660400 := by
    simpa [prefixWord, tailWord_3660400, baseEnd_3660400] using wordTrace_append hprefix tailTrace_3660400
  have hstable : (prefixWord ++ tailWord_3660400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660400).length < 2 ^ (prefixWord ++ tailWord_3660400).sum := by decide
  have hdescent : baseEnd_3660400 < baseStart_3660400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660444 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_3660444 : Nat := 118140960795 + 3660444 * 2 ^ 59
def prefixEnd_3660444 : Nat := 4983230072969 + 3 ^ 40 * 3660444 * 2
def baseEnd_3660444 : Nat := 1879567180866381729715931

theorem tailTrace_3660444 : CollatzResearch.WordTrace tailWord_3660444 prefixEnd_3660444 1879567180866381729715931 := by
  unfold tailWord_3660444
  simp only [CollatzResearch.WordTrace]
  refine ⟨66753680375422008454626193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89004907167229344606168257 66753680375422008454626193)
  ·
    refine ⟨50065260281566506340969645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66753680375422008454626193 50065260281566506340969645)
    ·
      refine ⟨18774472605587439877863617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50065260281566506340969645 18774472605587439877863617)
      ·
        refine ⟨14080854454190579908397713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18774472605587439877863617 14080854454190579908397713)
        ·
          refine ⟨10560640840642934931298285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14080854454190579908397713 10560640840642934931298285)
          ·
            refine ⟨3960240315241100599236857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10560640840642934931298285 3960240315241100599236857)
            ·
              refine ⟨2970180236430825449427643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960240315241100599236857 2970180236430825449427643)
              ·
                refine ⟨4455270354646238174141465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970180236430825449427643 4455270354646238174141465)
                ·
                  refine ⟨3341452765984678630606099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4455270354646238174141465 3341452765984678630606099)
                  ·
                    refine ⟨5012179148977017945909149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3341452765984678630606099 5012179148977017945909149)
                    ·
                      refine ⟨1879567180866381729715931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5012179148977017945909149 1879567180866381729715931)
                      ·
                        rfl

theorem cell23_3660444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_3660444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660444 prefixEnd_3660444 := by exact prefixLift 3660444
  have htrace : WordTrace (prefixWord ++ tailWord_3660444) baseStart_3660444 baseEnd_3660444 := by
    simpa [prefixWord, tailWord_3660444, baseEnd_3660444] using wordTrace_append hprefix tailTrace_3660444
  have hstable : (prefixWord ++ tailWord_3660444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660444).length < 2 ^ (prefixWord ++ tailWord_3660444).sum := by decide
  have hdescent : baseEnd_3660444 < baseStart_3660444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660473 : List Nat := [1, 2, 1, 4, 1, 1, 1, 7, 5]
def baseStart_3660473 : Nat := 118140960795 + 3660473 * 2 ^ 59
def prefixEnd_3660473 : Nat := 4983230072969 + 3 ^ 40 * 3660473 * 2
def baseEnd_3660473 : Nat := 208842452422818012917033

theorem tailTrace_3660473 : CollatzResearch.WordTrace tailWord_3660473 prefixEnd_3660473 208842452422818012917033 := by
  unfold tailWord_3660473
  simp only [CollatzResearch.WordTrace]
  refine ⟨133508418467738954862058073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89005612311825969908038715 133508418467738954862058073)
  ·
    refine ⟨100131313850804216146543555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133508418467738954862058073 100131313850804216146543555)
    ·
      refine ⟨150196970776206324219815333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100131313850804216146543555 150196970776206324219815333)
      ·
        refine ⟨28161932020538685791215375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150196970776206324219815333 28161932020538685791215375)
        ·
          refine ⟨42242898030808028686823063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28161932020538685791215375 42242898030808028686823063)
          ·
            refine ⟨63364347046212043030234595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42242898030808028686823063 63364347046212043030234595)
            ·
              refine ⟨95046520569318064545351893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63364347046212043030234595 95046520569318064545351893)
              ·
                refine ⟨2227652825843392137781685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95046520569318064545351893 2227652825843392137781685)
                ·
                  refine ⟨208842452422818012917033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227652825843392137781685 208842452422818012917033)
                  ·
                    rfl

theorem cell23_3660473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 5].length) (baseStart_3660473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660473 prefixEnd_3660473 := by exact prefixLift 3660473
  have htrace : WordTrace (prefixWord ++ tailWord_3660473) baseStart_3660473 baseEnd_3660473 := by
    simpa [prefixWord, tailWord_3660473, baseEnd_3660473] using wordTrace_append hprefix tailTrace_3660473
  have hstable : (prefixWord ++ tailWord_3660473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660473).length < 2 ^ (prefixWord ++ tailWord_3660473).sum := by decide
  have hdescent : baseEnd_3660473 < baseStart_3660473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660484 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_3660484 : Nat := 118140960795 + 3660484 * 2 ^ 59
def prefixEnd_3660484 : Nat := 4983230072969 + 3 ^ 40 * 3660484 * 2
def baseEnd_3660484 : Nat := 1879587720092561573215747

theorem tailTrace_3660484 : CollatzResearch.WordTrace tailWord_3660484 prefixEnd_3660484 1879587720092561573215747 := by
  unfold tailWord_3660484
  simp only [CollatzResearch.WordTrace]
  refine ⟨66754409835349551870354253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89005879780466069160472337 66754409835349551870354253)
  ·
    refine ⟨25032903688256081951382845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66754409835349551870354253 25032903688256081951382845)
    ·
      refine ⟨9387338883096030731768567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25032903688256081951382845 9387338883096030731768567)
      ·
        refine ⟨14081008324644046097652851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9387338883096030731768567 14081008324644046097652851)
        ·
          refine ⟨21121512486966069146479277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14081008324644046097652851 21121512486966069146479277)
          ·
            refine ⟨7920567182612275929929729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21121512486966069146479277 7920567182612275929929729)
            ·
              refine ⟨5940425386959206947447297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7920567182612275929929729 5940425386959206947447297)
              ·
                refine ⟨4455319040219405210585473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5940425386959206947447297 4455319040219405210585473)
                ·
                  refine ⟨3341489280164553907939105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4455319040219405210585473 3341489280164553907939105)
                  ·
                    refine ⟨2506116960123415430954329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3341489280164553907939105 2506116960123415430954329)
                    ·
                      refine ⟨1879587720092561573215747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506116960123415430954329 1879587720092561573215747)
                      ·
                        rfl

theorem cell23_3660484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_3660484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660484 prefixEnd_3660484 := by exact prefixLift 3660484
  have htrace : WordTrace (prefixWord ++ tailWord_3660484) baseStart_3660484 baseEnd_3660484 := by
    simpa [prefixWord, tailWord_3660484, baseEnd_3660484] using wordTrace_append hprefix tailTrace_3660484
  have hstable : (prefixWord ++ tailWord_3660484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660484).length < 2 ^ (prefixWord ++ tailWord_3660484).sum := by decide
  have hdescent : baseEnd_3660484 < baseStart_3660484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660490 : List Nat := [3, 1, 2, 1, 4, 2, 1, 4, 5]
def baseStart_3660490 : Nat := 118140960795 + 3660490 * 2 ^ 59
def prefixEnd_3660490 : Nat := 4983230072969 + 3 ^ 40 * 3660490 * 2
def baseEnd_3660490 : Nat := 208843422330720949971191

theorem tailTrace_3660490 : CollatzResearch.WordTrace tailWord_3660490 prefixEnd_3660490 208843422330720949971191 := by
  unfold tailWord_3660490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33377259627169341691356731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89006025672451577843617949 33377259627169341691356731)
  ·
    refine ⟨50065889440754012537035097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33377259627169341691356731 50065889440754012537035097)
    ·
      refine ⟨37549417080565509402776323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50065889440754012537035097 37549417080565509402776323)
      ·
        refine ⟨56324125620848264104164485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37549417080565509402776323 56324125620848264104164485)
        ·
          refine ⟨10560773553909049519530841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56324125620848264104164485 10560773553909049519530841)
          ·
            refine ⟨7920580165431787139648131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10560773553909049519530841 7920580165431787139648131)
            ·
              refine ⟨11880870248147680709472197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7920580165431787139648131 11880870248147680709472197)
              ·
                refine ⟨2227663171527690133026037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11880870248147680709472197 2227663171527690133026037)
                ·
                  refine ⟨208843422330720949971191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227663171527690133026037 208843422330720949971191)
                  ·
                    rfl

theorem cell23_3660490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_3660490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660490 prefixEnd_3660490 := by exact prefixLift 3660490
  have htrace : WordTrace (prefixWord ++ tailWord_3660490) baseStart_3660490 baseEnd_3660490 := by
    simpa [prefixWord, tailWord_3660490, baseEnd_3660490] using wordTrace_append hprefix tailTrace_3660490
  have hstable : (prefixWord ++ tailWord_3660490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660490).length < 2 ^ (prefixWord ++ tailWord_3660490).sum := by decide
  have hdescent : baseEnd_3660490 < baseStart_3660490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660523 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 3, 6, 2]
def baseStart_3660523 : Nat := 118140960795 + 3660523 * 2 ^ 59
def prefixEnd_3660523 : Nat := 4983230072969 + 3 ^ 40 * 3660523 * 2
def baseEnd_3660523 : Nat := 1879607745838086920628067

theorem tailTrace_3660523 : CollatzResearch.WordTrace tailWord_3660523 prefixEnd_3660523 1879607745838086920628067 := by
  unfold tailWord_3660523
  simp only [CollatzResearch.WordTrace]
  refine ⟨133510242117557813401378223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89006828078371875600918815 133510242117557813401378223)
  ·
    refine ⟨200265363176336720102067335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133510242117557813401378223 200265363176336720102067335)
    ·
      refine ⟨300398044764505080153101003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200265363176336720102067335 300398044764505080153101003)
      ·
        refine ⟨450597067146757620229651505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300398044764505080153101003 450597067146757620229651505)
        ·
          refine ⟨337947800360068215172238629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450597067146757620229651505 337947800360068215172238629)
          ·
            refine ⟨63365212567512790344794743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337947800360068215172238629 63365212567512790344794743)
            ·
              refine ⟨95047818851269185517192115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63365212567512790344794743 95047818851269185517192115)
              ·
                refine ⟨142571728276903778275788173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95047818851269185517192115 142571728276903778275788173)
                ·
                  refine ⟨53464398103838916853420565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142571728276903778275788173 53464398103838916853420565)
                  ·
                    refine ⟨2506143661117449227504089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53464398103838916853420565 2506143661117449227504089)
                    ·
                      refine ⟨1879607745838086920628067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506143661117449227504089 1879607745838086920628067)
                      ·
                        rfl

theorem cell23_3660523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 6, 2].length) (baseStart_3660523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660523 prefixEnd_3660523 := by exact prefixLift 3660523
  have htrace : WordTrace (prefixWord ++ tailWord_3660523) baseStart_3660523 baseEnd_3660523 := by
    simpa [prefixWord, tailWord_3660523, baseEnd_3660523] using wordTrace_append hprefix tailTrace_3660523
  have hstable : (prefixWord ++ tailWord_3660523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660523).length < 2 ^ (prefixWord ++ tailWord_3660523).sum := by decide
  have hdescent : baseEnd_3660523 < baseStart_3660523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660536 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_3660536 : Nat := 118140960795 + 3660536 * 2 ^ 59
def prefixEnd_3660536 : Nat := 4983230072969 + 3 ^ 40 * 3660536 * 2
def baseEnd_3660536 : Nat := 1879614421086595369765507

theorem tailTrace_3660536 : CollatzResearch.WordTrace tailWord_3660536 prefixEnd_3660536 1879614421086595369765507 := by
  unfold tailWord_3660536
  simp only [CollatzResearch.WordTrace]
  refine ⟨66755358133255358310800731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89007144177673811081067641 66755358133255358310800731)
  ·
    refine ⟨100133037199883037466201097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66755358133255358310800731 100133037199883037466201097)
    ·
      refine ⟨75099777899912278099650823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100133037199883037466201097 75099777899912278099650823)
      ·
        refine ⟨112649666849868417149476235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75099777899912278099650823 112649666849868417149476235)
        ·
          refine ⟨168974500274802625724214353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112649666849868417149476235 168974500274802625724214353)
          ·
            refine ⟨126730875206101969293160765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168974500274802625724214353 126730875206101969293160765)
            ·
              refine ⟨47524078202288238484935287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126730875206101969293160765 47524078202288238484935287)
              ·
                refine ⟨71286117303432357727402931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47524078202288238484935287 71286117303432357727402931)
                ·
                  refine ⟨106929175955148536591104397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71286117303432357727402931 106929175955148536591104397)
                  ·
                    refine ⟨40098440983180701221664149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106929175955148536591104397 40098440983180701221664149)
                    ·
                      refine ⟨1879614421086595369765507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40098440983180701221664149 1879614421086595369765507)
                      ·
                        rfl

theorem cell23_3660536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_3660536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660536 prefixEnd_3660536 := by exact prefixLift 3660536
  have htrace : WordTrace (prefixWord ++ tailWord_3660536) baseStart_3660536 baseEnd_3660536 := by
    simpa [prefixWord, tailWord_3660536, baseEnd_3660536] using wordTrace_append hprefix tailTrace_3660536
  have hstable : (prefixWord ++ tailWord_3660536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660536).length < 2 ^ (prefixWord ++ tailWord_3660536).sum := by decide
  have hdescent : baseEnd_3660536 < baseStart_3660536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660540 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_3660540 : Nat := 118140960795 + 3660540 * 2 ^ 59
def prefixEnd_3660540 : Nat := 4983230072969 + 3 ^ 40 * 3660540 * 2
def baseEnd_3660540 : Nat := 1879616475009213354115489

theorem tailTrace_3660540 : CollatzResearch.WordTrace tailWord_3660540 prefixEnd_3660540 1879616475009213354115489 := by
  unfold tailWord_3660540
  simp only [CollatzResearch.WordTrace]
  refine ⟨66755431079248112652373537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89007241438997483536498049 66755431079248112652373537)
  ·
    refine ⟨50066573309436084489280153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66755431079248112652373537 50066573309436084489280153)
    ·
      refine ⟨37549929982077063366960115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50066573309436084489280153 37549929982077063366960115)
      ·
        refine ⟨56324894973115595050440173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37549929982077063366960115 56324894973115595050440173)
        ·
          refine ⟨21121835614918348143915065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56324894973115595050440173 21121835614918348143915065)
          ·
            refine ⟨15841376711188761107936299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21121835614918348143915065 15841376711188761107936299)
            ·
              refine ⟨23762065066783141661904449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15841376711188761107936299 23762065066783141661904449)
              ·
                refine ⟨17821548800087356246428337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23762065066783141661904449 17821548800087356246428337)
                ·
                  refine ⟨13366161600065517184821253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17821548800087356246428337 13366161600065517184821253)
                  ·
                    refine ⟨2506155300012284472153985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13366161600065517184821253 2506155300012284472153985)
                    ·
                      refine ⟨1879616475009213354115489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506155300012284472153985 1879616475009213354115489)
                      ·
                        rfl

theorem cell23_3660540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_3660540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660540 prefixEnd_3660540 := by exact prefixLift 3660540
  have htrace : WordTrace (prefixWord ++ tailWord_3660540) baseStart_3660540 baseEnd_3660540 := by
    simpa [prefixWord, tailWord_3660540, baseEnd_3660540] using wordTrace_append hprefix tailTrace_3660540
  have hstable : (prefixWord ++ tailWord_3660540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660540).length < 2 ^ (prefixWord ++ tailWord_3660540).sum := by decide
  have hdescent : baseEnd_3660540 < baseStart_3660540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660543 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 3]
def baseStart_3660543 : Nat := 118140960795 + 3660543 * 2 ^ 59
def prefixEnd_3660543 : Nat := 4983230072969 + 3 ^ 40 * 3660543 * 2
def baseEnd_3660543 : Nat := 1879618015451176842377975

theorem tailTrace_3660543 : CollatzResearch.WordTrace tailWord_3660543 prefixEnd_3660543 1879618015451176842377975 := by
  unfold tailWord_3660543
  simp only [CollatzResearch.WordTrace]
  refine ⟨133510971577485356817106283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89007314384990237878070855 133510971577485356817106283)
  ·
    refine ⟨200266457366228035225659425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133510971577485356817106283 200266457366228035225659425)
    ·
      refine ⟨150199843024671026419244569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200266457366228035225659425 150199843024671026419244569)
      ·
        refine ⟨112649882268503269814433427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150199843024671026419244569 112649882268503269814433427)
        ·
          refine ⟨168974823402754904721650141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112649882268503269814433427 168974823402754904721650141)
          ·
            refine ⟨63365558776033089270618803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168974823402754904721650141 63365558776033089270618803)
            ·
              refine ⟨95048338164049633905928205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63365558776033089270618803 95048338164049633905928205)
              ·
                refine ⟨35643126811518612714723077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95048338164049633905928205 35643126811518612714723077)
                ·
                  refine ⟨6683086277159739884010577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35643126811518612714723077 6683086277159739884010577)
                  ·
                    refine ⟨5012314707869804913007933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6683086277159739884010577 5012314707869804913007933)
                    ·
                      refine ⟨1879618015451176842377975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5012314707869804913007933 1879618015451176842377975)
                      ·
                        rfl

theorem cell23_3660543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_3660543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660543 prefixEnd_3660543 := by exact prefixLift 3660543
  have htrace : WordTrace (prefixWord ++ tailWord_3660543) baseStart_3660543 baseEnd_3660543 := by
    simpa [prefixWord, tailWord_3660543, baseEnd_3660543] using wordTrace_append hprefix tailTrace_3660543
  have hstable : (prefixWord ++ tailWord_3660543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660543).length < 2 ^ (prefixWord ++ tailWord_3660543).sum := by decide
  have hdescent : baseEnd_3660543 < baseStart_3660543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660607 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 3]
def baseStart_3660607 : Nat := 118140960795 + 3660607 * 2 ^ 59
def prefixEnd_3660607 : Nat := 4983230072969 + 3 ^ 40 * 3660607 * 2
def baseEnd_3660607 : Nat := 1879650878213064591977681

theorem tailTrace_3660607 : CollatzResearch.WordTrace tailWord_3660607 prefixEnd_3660607 1879650878213064591977681 := by
  unfold tailWord_3660607
  simp only [CollatzResearch.WordTrace]
  refine ⟨133513305849253495747436075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89008870566168997164957383 133513305849253495747436075)
  ·
    refine ⟨200269958773880243621154113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133513305849253495747436075 200269958773880243621154113)
    ·
      refine ⟨150202469080410182715865585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200269958773880243621154113 150202469080410182715865585)
      ·
        refine ⟨112651851810307637036899189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150202469080410182715865585 112651851810307637036899189)
        ·
          refine ⟨10561111107216340972209299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112651851810307637036899189 10561111107216340972209299)
          ·
            refine ⟨15841666660824511458313949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10561111107216340972209299 15841666660824511458313949)
            ·
              refine ⟨5940624997809191796867731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15841666660824511458313949 5940624997809191796867731)
              ·
                refine ⟨8910937496713787695301597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5940624997809191796867731 8910937496713787695301597)
                ·
                  refine ⟨3341601561267670385738099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8910937496713787695301597 3341601561267670385738099)
                  ·
                    refine ⟨5012402341901505578607149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3341601561267670385738099 5012402341901505578607149)
                    ·
                      refine ⟨1879650878213064591977681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5012402341901505578607149 1879650878213064591977681)
                      ·
                        rfl

theorem cell23_3660607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_3660607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660607 prefixEnd_3660607 := by exact prefixLift 3660607
  have htrace : WordTrace (prefixWord ++ tailWord_3660607) baseStart_3660607 baseEnd_3660607 := by
    simpa [prefixWord, tailWord_3660607, baseEnd_3660607] using wordTrace_append hprefix tailTrace_3660607
  have hstable : (prefixWord ++ tailWord_3660607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660607).length < 2 ^ (prefixWord ++ tailWord_3660607).sum := by decide
  have hdescent : baseEnd_3660607 < baseStart_3660607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660614 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_3660614 : Nat := 118140960795 + 3660614 * 2 ^ 59
def prefixEnd_3660614 : Nat := 4983230072969 + 3 ^ 40 * 3660614 * 2
def baseEnd_3660614 : Nat := 208850496953071784954461

theorem tailTrace_3660614 : CollatzResearch.WordTrace tailWord_3660614 prefixEnd_3660614 208850496953071784954461 := by
  unfold tailWord_3660614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172298786257129248216903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89009040773485423961960597 4172298786257129248216903)
  ·
    refine ⟨6258448179385693872325355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4172298786257129248216903 6258448179385693872325355)
    ·
      refine ⟨9387672269078540808488033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6258448179385693872325355 9387672269078540808488033)
      ·
        refine ⟨7040754201808905606366025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9387672269078540808488033 7040754201808905606366025)
        ·
          refine ⟨5280565651356679204774519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7040754201808905606366025 5280565651356679204774519)
          ·
            refine ⟨7920848477035018807161779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280565651356679204774519 7920848477035018807161779)
            ·
              refine ⟨11881272715552528210742669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7920848477035018807161779 11881272715552528210742669)
              ·
                refine ⟨4455477268332198079028501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11881272715552528210742669 4455477268332198079028501)
                ·
                  refine ⟨208850496953071784954461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4455477268332198079028501 208850496953071784954461)
                  ·
                    rfl

theorem cell23_3660614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_3660614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660614 prefixEnd_3660614 := by exact prefixLift 3660614
  have htrace : WordTrace (prefixWord ++ tailWord_3660614) baseStart_3660614 baseEnd_3660614 := by
    simpa [prefixWord, tailWord_3660614, baseEnd_3660614] using wordTrace_append hprefix tailTrace_3660614
  have hstable : (prefixWord ++ tailWord_3660614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660614).length < 2 ^ (prefixWord ++ tailWord_3660614).sum := by decide
  have hdescent : baseEnd_3660614 < baseStart_3660614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660657 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 2, 4]
def baseStart_3660657 : Nat := 118140960795 + 3660657 * 2 ^ 59
def prefixEnd_3660657 : Nat := 4983230072969 + 3 ^ 40 * 3660657 * 2
def baseEnd_3660657 : Nat := 626558850748596465450817

theorem tailTrace_3660657 : CollatzResearch.WordTrace tailWord_3660657 prefixEnd_3660657 626558850748596465450817 := by
  unfold tailWord_3660657
  simp only [CollatzResearch.WordTrace]
  refine ⟨133515129499072354286756225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89010086332714902857837483 133515129499072354286756225)
  ·
    refine ⟨100136347124304265715067169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133515129499072354286756225 100136347124304265715067169)
    ·
      refine ⟨75102260343228199286300377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100136347124304265715067169 75102260343228199286300377)
      ·
        refine ⟨56326695257421149464725283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75102260343228199286300377 56326695257421149464725283)
        ·
          refine ⟨84490042886131724197087925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56326695257421149464725283 84490042886131724197087925)
          ·
            refine ⟨7920941520574849143476993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84490042886131724197087925 7920941520574849143476993)
            ·
              refine ⟨5940706140431136857607745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7920941520574849143476993 5940706140431136857607745)
              ·
                refine ⟨4455529605323352643205809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5940706140431136857607745 4455529605323352643205809)
                ·
                  refine ⟨3341647203992514482404357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4455529605323352643205809 3341647203992514482404357)
                  ·
                    refine ⟨626558850748596465450817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3341647203992514482404357 626558850748596465450817)
                    ·
                      rfl

theorem cell23_3660657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_3660657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660657 prefixEnd_3660657 := by exact prefixLift 3660657
  have htrace : WordTrace (prefixWord ++ tailWord_3660657) baseStart_3660657 baseEnd_3660657 := by
    simpa [prefixWord, tailWord_3660657, baseEnd_3660657] using wordTrace_append hprefix tailTrace_3660657
  have hstable : (prefixWord ++ tailWord_3660657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660657).length < 2 ^ (prefixWord ++ tailWord_3660657).sum := by decide
  have hdescent : baseEnd_3660657 < baseStart_3660657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660698 : List Nat := [3, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2]
def baseStart_3660698 : Nat := 118140960795 + 3660698 * 2 ^ 59
def prefixEnd_3660698 : Nat := 4983230072969 + 3 ^ 40 * 3660698 * 2
def baseEnd_3660698 : Nat := 1879697604952623735939763

theorem tailTrace_3660698 : CollatzResearch.WordTrace tailWord_3660698 prefixEnd_3660698 1879697604952623735939763 := by
  unfold tailWord_3660698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33379156222980954572249687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89011083261282545525999165 33379156222980954572249687)
  ·
    refine ⟨50068734334471431858374531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33379156222980954572249687 50068734334471431858374531)
    ·
      refine ⟨75103101501707147787561797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50068734334471431858374531 75103101501707147787561797)
      ·
        refine ⟨14081831531570090210167837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75103101501707147787561797 14081831531570090210167837)
        ·
          refine ⟨5280686824338783828812939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14081831531570090210167837 5280686824338783828812939)
          ·
            refine ⟨7921030236508175743219409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280686824338783828812939 7921030236508175743219409)
            ·
              refine ⟨5940772677381131807414557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7921030236508175743219409 5940772677381131807414557)
              ·
                refine ⟨2227789754017924427780459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5940772677381131807414557 2227789754017924427780459)
                ·
                  refine ⟨3341684631026886641670689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227789754017924427780459 3341684631026886641670689)
                  ·
                    refine ⟨2506263473270164981253017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3341684631026886641670689 2506263473270164981253017)
                    ·
                      refine ⟨1879697604952623735939763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506263473270164981253017 1879697604952623735939763)
                      ·
                        rfl

theorem cell23_3660698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_3660698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660698 prefixEnd_3660698 := by exact prefixLift 3660698
  have htrace : WordTrace (prefixWord ++ tailWord_3660698) baseStart_3660698 baseEnd_3660698 := by
    simpa [prefixWord, tailWord_3660698, baseEnd_3660698] using wordTrace_append hprefix tailTrace_3660698
  have hstable : (prefixWord ++ tailWord_3660698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660698).length < 2 ^ (prefixWord ++ tailWord_3660698).sum := by decide
  have hdescent : baseEnd_3660698 < baseStart_3660698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660713 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 4, 6]
def baseStart_3660713 : Nat := 118140960795 + 3660713 * 2 ^ 59
def prefixEnd_3660713 : Nat := 4983230072969 + 3 ^ 40 * 3660713 * 2
def baseEnd_3660713 : Nat := 626568435720813725750731

theorem tailTrace_3660713 : CollatzResearch.WordTrace tailWord_3660713 prefixEnd_3660713 626568435720813725750731 := by
  unfold tailWord_3660713
  simp only [CollatzResearch.WordTrace]
  refine ⟨133517171986869475850794793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89011447991246317233863195 133517171986869475850794793)
  ·
    refine ⟨100137878990152106888096095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133517171986869475850794793 100137878990152106888096095)
    ·
      refine ⟨150206818485228160332144143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100137878990152106888096095 150206818485228160332144143)
      ·
        refine ⟨225310227727842240498216215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150206818485228160332144143 225310227727842240498216215)
        ·
          refine ⟨337965341591763360747324323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225310227727842240498216215 337965341591763360747324323)
          ·
            refine ⟨506948012387645041120986485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337965341591763360747324323 506948012387645041120986485)
            ·
              refine ⟨47526376161341722605092483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506948012387645041120986485 47526376161341722605092483)
              ·
                refine ⟨71289564242012583907638725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47526376161341722605092483 71289564242012583907638725)
                ·
                  refine ⟨13366793295377359482682261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71289564242012583907638725 13366793295377359482682261)
                  ·
                    refine ⟨626568435720813725750731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13366793295377359482682261 626568435720813725750731)
                    ·
                      rfl

theorem cell23_3660713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_3660713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660713 prefixEnd_3660713 := by exact prefixLift 3660713
  have htrace : WordTrace (prefixWord ++ tailWord_3660713) baseStart_3660713 baseEnd_3660713 := by
    simpa [prefixWord, tailWord_3660713, baseEnd_3660713] using wordTrace_append hprefix tailTrace_3660713
  have hstable : (prefixWord ++ tailWord_3660713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660713).length < 2 ^ (prefixWord ++ tailWord_3660713).sum := by decide
  have hdescent : baseEnd_3660713 < baseStart_3660713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660720 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 10, 2]
def baseStart_3660720 : Nat := 118140960795 + 3660720 * 2 ^ 59
def prefixEnd_3660720 : Nat := 4983230072969 + 3 ^ 40 * 3660720 * 2
def baseEnd_3660720 : Nat := 1879708901527022649864661

theorem tailTrace_3660720 : CollatzResearch.WordTrace tailWord_3660720 prefixEnd_3660720 1879708901527022649864661 := by
  unfold tailWord_3660720
  simp only [CollatzResearch.WordTrace]
  refine ⟨66758713648922058023149807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89011618198562744030866409 66758713648922058023149807)
  ·
    refine ⟨100138070473383087034724711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66758713648922058023149807 100138070473383087034724711)
    ·
      refine ⟨150207105710074630552087067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100138070473383087034724711 150207105710074630552087067)
      ·
        refine ⟨225310658565111945828130601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150207105710074630552087067 225310658565111945828130601)
        ·
          refine ⟨168982993923833959371097951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225310658565111945828130601 168982993923833959371097951)
          ·
            refine ⟨253474490885750939056646927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168982993923833959371097951 253474490885750939056646927)
            ·
              refine ⟨380211736328626408584970391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253474490885750939056646927 380211736328626408584970391)
              ·
                refine ⟨570317604492939612877455587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380211736328626408584970391 570317604492939612877455587)
                ·
                  refine ⟨855476406739409419316183381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570317604492939612877455587 855476406739409419316183381)
                  ·
                    refine ⟨2506278535369363533152881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 855476406739409419316183381 2506278535369363533152881)
                    ·
                      refine ⟨1879708901527022649864661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506278535369363533152881 1879708901527022649864661)
                      ·
                        rfl

theorem cell23_3660720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 10, 2].length) (baseStart_3660720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660720 prefixEnd_3660720 := by exact prefixLift 3660720
  have htrace : WordTrace (prefixWord ++ tailWord_3660720) baseStart_3660720 baseEnd_3660720 := by
    simpa [prefixWord, tailWord_3660720, baseEnd_3660720] using wordTrace_append hprefix tailTrace_3660720
  have hstable : (prefixWord ++ tailWord_3660720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660720).length < 2 ^ (prefixWord ++ tailWord_3660720).sum := by decide
  have hdescent : baseEnd_3660720 < baseStart_3660720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660723 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 5]
def baseStart_3660723 : Nat := 118140960795 + 3660723 * 2 ^ 59
def prefixEnd_3660723 : Nat := 4983230072969 + 3 ^ 40 * 3660723 * 2
def baseEnd_3660723 : Nat := 1879710441968986138127147

theorem tailTrace_3660723 : CollatzResearch.WordTrace tailWord_3660723 prefixEnd_3660723 1879710441968986138127147 := by
  unfold tailWord_3660723
  simp only [CollatzResearch.WordTrace]
  refine ⟨133517536716833247558658823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89011691144555498372439215 133517536716833247558658823)
  ·
    refine ⟨200276305075249871337988235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133517536716833247558658823 200276305075249871337988235)
    ·
      refine ⟨300414457612874807006982353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200276305075249871337988235 300414457612874807006982353)
      ·
        refine ⟨225310843209656105255236765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300414457612874807006982353 225310843209656105255236765)
        ·
          refine ⟨84491566203621039470713787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225310843209656105255236765 84491566203621039470713787)
          ·
            refine ⟨126737349305431559206070681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84491566203621039470713787 126737349305431559206070681)
            ·
              refine ⟨95053011979073669404553011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126737349305431559206070681 95053011979073669404553011)
              ·
                refine ⟨142579517968610504106829517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95053011979073669404553011 142579517968610504106829517)
                ·
                  refine ⟨53467319238228939040061069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142579517968610504106829517 53467319238228939040061069)
                  ·
                    refine ⟨20050244714335852140022901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53467319238228939040061069 20050244714335852140022901)
                    ·
                      refine ⟨1879710441968986138127147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20050244714335852140022901 1879710441968986138127147)
                      ·
                        rfl

theorem cell23_3660723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_3660723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660723 prefixEnd_3660723 := by exact prefixLift 3660723
  have htrace : WordTrace (prefixWord ++ tailWord_3660723) baseStart_3660723 baseEnd_3660723 := by
    simpa [prefixWord, tailWord_3660723, baseEnd_3660723] using wordTrace_append hprefix tailTrace_3660723
  have hstable : (prefixWord ++ tailWord_3660723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660723).length < 2 ^ (prefixWord ++ tailWord_3660723).sum := by decide
  have hdescent : baseEnd_3660723 < baseStart_3660723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660749 : List Nat := [1, 6, 3, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3660749 : Nat := 118140960795 + 3660749 * 2 ^ 59
def prefixEnd_3660749 : Nat := 4983230072969 + 3 ^ 40 * 3660749 * 2
def baseEnd_3660749 : Nat := 1879723792466003036402029

theorem tailTrace_3660749 : CollatzResearch.WordTrace tailWord_3660749 prefixEnd_3660749 1879723792466003036402029 := by
  unfold tailWord_3660749
  simp only [CollatzResearch.WordTrace]
  refine ⟨133518485014739053999105301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89012323343159369332736867 133518485014739053999105301)
  ·
    refine ⟨6258678985065893156208061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133518485014739053999105301 6258678985065893156208061)
    ·
      refine ⟨2347004619399709933578023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6258678985065893156208061 2347004619399709933578023)
      ·
        refine ⟨3520506929099564900367035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2347004619399709933578023 3520506929099564900367035)
        ·
          refine ⟨5280760393649347350550553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520506929099564900367035 5280760393649347350550553)
          ·
            refine ⟨3960570295237010512912915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5280760393649347350550553 3960570295237010512912915)
            ·
              refine ⟨5940855442855515769369373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960570295237010512912915 5940855442855515769369373)
              ·
                refine ⟨2227820791070818413513515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5940855442855515769369373 2227820791070818413513515)
                ·
                  refine ⟨3341731186606227620270273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227820791070818413513515 3341731186606227620270273)
                  ·
                    refine ⟨2506298389954670715202705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3341731186606227620270273 2506298389954670715202705)
                    ·
                      refine ⟨1879723792466003036402029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506298389954670715202705 1879723792466003036402029)
                      ·
                        rfl

theorem cell23_3660749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3660749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660749 prefixEnd_3660749 := by exact prefixLift 3660749
  have htrace : WordTrace (prefixWord ++ tailWord_3660749) baseStart_3660749 baseEnd_3660749 := by
    simpa [prefixWord, tailWord_3660749, baseEnd_3660749] using wordTrace_append hprefix tailTrace_3660749
  have hstable : (prefixWord ++ tailWord_3660749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660749).length < 2 ^ (prefixWord ++ tailWord_3660749).sum := by decide
  have hdescent : baseEnd_3660749 < baseStart_3660749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660757 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3660757 : Nat := 118140960795 + 3660757 * 2 ^ 59
def prefixEnd_3660757 : Nat := 4983230072969 + 3 ^ 40 * 3660757 * 2
def baseEnd_3660757 : Nat := 1879727900311239005101991

theorem tailTrace_3660757 : CollatzResearch.WordTrace tailWord_3660757 prefixEnd_3660757 1879727900311239005101991 := by
  unfold tailWord_3660757
  simp only [CollatzResearch.WordTrace]
  refine ⟨133518776798710071365396525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89012517865806714243597683 133518776798710071365396525)
  ·
    refine ⟨50069541299516276762023697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133518776798710071365396525 50069541299516276762023697)
    ·
      refine ⟨37552155974637207571517773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50069541299516276762023697 37552155974637207571517773)
      ·
        refine ⟨14082058490488952839319165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37552155974637207571517773 14082058490488952839319165)
        ·
          refine ⟨5280771933933357314744687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14082058490488952839319165 5280771933933357314744687)
          ·
            refine ⟨7921157900900035972117031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280771933933357314744687 7921157900900035972117031)
            ·
              refine ⟨11881736851350053958175547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7921157900900035972117031 11881736851350053958175547)
              ·
                refine ⟨17822605277025080937263321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11881736851350053958175547 17822605277025080937263321)
                ·
                  refine ⟨13366953957768810702947491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17822605277025080937263321 13366953957768810702947491)
                  ·
                    refine ⟨20050430936653216054421237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13366953957768810702947491 20050430936653216054421237)
                    ·
                      refine ⟨1879727900311239005101991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20050430936653216054421237 1879727900311239005101991)
                      ·
                        rfl

theorem cell23_3660757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3660757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660757 prefixEnd_3660757 := by exact prefixLift 3660757
  have htrace : WordTrace (prefixWord ++ tailWord_3660757) baseStart_3660757 baseEnd_3660757 := by
    simpa [prefixWord, tailWord_3660757, baseEnd_3660757] using wordTrace_append hprefix tailTrace_3660757
  have hstable : (prefixWord ++ tailWord_3660757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660757).length < 2 ^ (prefixWord ++ tailWord_3660757).sum := by decide
  have hdescent : baseEnd_3660757 < baseStart_3660757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660807 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 2, 5]
def baseStart_3660807 : Nat := 118140960795 + 3660807 * 2 ^ 59
def prefixEnd_3660807 : Nat := 4983230072969 + 3 ^ 40 * 3660807 * 2
def baseEnd_3660807 : Nat := 626584524781321269825587

theorem tailTrace_3660807 : CollatzResearch.WordTrace tailWord_3660807 prefixEnd_3660807 626584524781321269825587 := by
  unfold tailWord_3660807
  simp only [CollatzResearch.WordTrace]
  refine ⟨133520600448528929904716675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89013733632352619936477783 133520600448528929904716675)
  ·
    refine ⟨200280900672793394857075013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133520600448528929904716675 200280900672793394857075013)
    ·
      refine ⟨37552668876148761535701565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200280900672793394857075013 37552668876148761535701565)
      ·
        refine ⟨14082250828555785575888087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37552668876148761535701565 14082250828555785575888087)
        ·
          refine ⟨21123376242833678363832131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14082250828555785575888087 21123376242833678363832131)
          ·
            refine ⟨31685064364250517545748197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21123376242833678363832131 31685064364250517545748197)
            ·
              refine ⟨5940949568296972039827787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31685064364250517545748197 5940949568296972039827787)
              ·
                refine ⟨8911424352445458059741681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5940949568296972039827787 8911424352445458059741681)
                ·
                  refine ⟨6683568264334093544806261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8911424352445458059741681 6683568264334093544806261)
                  ·
                    refine ⟨626584524781321269825587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6683568264334093544806261 626584524781321269825587)
                    ·
                      rfl

theorem cell23_3660807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_3660807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660807 prefixEnd_3660807 := by exact prefixLift 3660807
  have htrace : WordTrace (prefixWord ++ tailWord_3660807) baseStart_3660807 baseEnd_3660807 := by
    simpa [prefixWord, tailWord_3660807, baseEnd_3660807] using wordTrace_append hprefix tailTrace_3660807
  have hstable : (prefixWord ++ tailWord_3660807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660807).length < 2 ^ (prefixWord ++ tailWord_3660807).sum := by decide
  have hdescent : baseEnd_3660807 < baseStart_3660807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660828 : List Nat := [2, 2, 3, 1, 5, 1, 2, 2, 5]
def baseStart_3660828 : Nat := 118140960795 + 3660828 * 2 ^ 59
def prefixEnd_3660828 : Nat := 4983230072969 + 3 ^ 40 * 3660828 * 2
def baseEnd_3660828 : Nat := 208862706381967580812685

theorem tailTrace_3660828 : CollatzResearch.WordTrace tailWord_3660828 prefixEnd_3660828 208862706381967580812685 := by
  unfold tailWord_3660828
  simp only [CollatzResearch.WordTrace]
  refine ⟨66760683190726425245615569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89014244254301900327487425 66760683190726425245615569)
  ·
    refine ⟨50070512393044818934211677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66760683190726425245615569 50070512393044818934211677)
    ·
      refine ⟨18776442147391807100329379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50070512393044818934211677 18776442147391807100329379)
      ·
        refine ⟨28164663221087710650494069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18776442147391807100329379 28164663221087710650494069)
        ·
          refine ⟨2640437176976972873483819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28164663221087710650494069 2640437176976972873483819)
          ·
            refine ⟨3960655765465459310225729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640437176976972873483819 3960655765465459310225729)
            ·
              refine ⟨2970491824099094482669297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960655765465459310225729 2970491824099094482669297)
              ·
                refine ⟨2227868868074320862001973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970491824099094482669297 2227868868074320862001973)
                ·
                  refine ⟨208862706381967580812685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2227868868074320862001973 208862706381967580812685)
                  ·
                    rfl

theorem cell23_3660828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_3660828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660828 prefixEnd_3660828 := by exact prefixLift 3660828
  have htrace : WordTrace (prefixWord ++ tailWord_3660828) baseStart_3660828 baseEnd_3660828 := by
    simpa [prefixWord, tailWord_3660828, baseEnd_3660828] using wordTrace_append hprefix tailTrace_3660828
  have hstable : (prefixWord ++ tailWord_3660828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660828).length < 2 ^ (prefixWord ++ tailWord_3660828).sum := by decide
  have hdescent : baseEnd_3660828 < baseStart_3660828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660837 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_3660837 : Nat := 118140960795 + 3660837 * 2 ^ 59
def prefixEnd_3660837 : Nat := 4983230072969 + 3 ^ 40 * 3660837 * 2
def baseEnd_3660837 : Nat := 626589659587866230700541

theorem tailTrace_3660837 : CollatzResearch.WordTrace tailWord_3660837 prefixEnd_3660837 626589659587866230700541 := by
  unfold tailWord_3660837
  simp only [CollatzResearch.WordTrace]
  refine ⟨133521694638420245028308765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89014463092280163352205843 133521694638420245028308765)
  ·
    refine ⟨50070635489407591885615787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133521694638420245028308765 50070635489407591885615787)
    ·
      refine ⟨75105953234111387828423681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50070635489407591885615787 75105953234111387828423681)
      ·
        refine ⟨56329464925583540871317761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75105953234111387828423681 56329464925583540871317761)
        ·
          refine ⟨42247098694187655653488321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56329464925583540871317761 42247098694187655653488321)
          ·
            refine ⟨31685324020640741740116241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42247098694187655653488321 31685324020640741740116241)
            ·
              refine ⟨23763993015480556305087181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31685324020640741740116241 23763993015480556305087181)
              ·
                refine ⟨8911497380805208614407693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23763993015480556305087181 8911497380805208614407693)
                ·
                  refine ⟨3341811517801953230402885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8911497380805208614407693 3341811517801953230402885)
                  ·
                    refine ⟨626589659587866230700541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3341811517801953230402885 626589659587866230700541)
                    ·
                      rfl

theorem cell23_3660837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_3660837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660837 prefixEnd_3660837 := by exact prefixLift 3660837
  have htrace : WordTrace (prefixWord ++ tailWord_3660837) baseStart_3660837 baseEnd_3660837 := by
    simpa [prefixWord, tailWord_3660837, baseEnd_3660837] using wordTrace_append hprefix tailTrace_3660837
  have hstable : (prefixWord ++ tailWord_3660837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660837).length < 2 ^ (prefixWord ++ tailWord_3660837).sum := by decide
  have hdescent : baseEnd_3660837 < baseStart_3660837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660854 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3660854 : Nat := 118140960795 + 3660854 * 2 ^ 59
def prefixEnd_3660854 : Nat := 4983230072969 + 3 ^ 40 * 3660854 * 2
def baseEnd_3660854 : Nat := 626592569311575041863015

theorem tailTrace_3660854 : CollatzResearch.WordTrace tailWord_3660854 prefixEnd_3660854 626592569311575041863015 := by
  unfold tailWord_3660854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8345144667459916058229851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89014876452905771287785077 8345144667459916058229851)
  ·
    refine ⟨12517717001189874087344777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8345144667459916058229851 12517717001189874087344777)
    ·
      refine ⟨9388287750892405565508583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12517717001189874087344777 9388287750892405565508583)
      ·
        refine ⟨14082431626338608348262875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9388287750892405565508583 14082431626338608348262875)
        ·
          refine ⟨21123647439507912522394313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14082431626338608348262875 21123647439507912522394313)
          ·
            refine ⟨15842735579630934391795735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21123647439507912522394313 15842735579630934391795735)
            ·
              refine ⟨23764103369446401587693603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15842735579630934391795735 23764103369446401587693603)
              ·
                refine ⟨35646155054169602381540405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23764103369446401587693603 35646155054169602381540405)
                ·
                  refine ⟨3341827036328400223269413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35646155054169602381540405 3341827036328400223269413)
                  ·
                    refine ⟨626592569311575041863015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3341827036328400223269413 626592569311575041863015)
                    ·
                      rfl

theorem cell23_3660854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3660854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660854 prefixEnd_3660854 := by exact prefixLift 3660854
  have htrace : WordTrace (prefixWord ++ tailWord_3660854) baseStart_3660854 baseEnd_3660854 := by
    simpa [prefixWord, tailWord_3660854, baseEnd_3660854] using wordTrace_append hprefix tailTrace_3660854
  have hstable : (prefixWord ++ tailWord_3660854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660854).length < 2 ^ (prefixWord ++ tailWord_3660854).sum := by decide
  have hdescent : baseEnd_3660854 < baseStart_3660854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660871 : List Nat := [1, 1, 4, 1, 3, 3, 2, 3, 1, 4]
def baseStart_3660871 : Nat := 118140960795 + 3660871 * 2 ^ 59
def prefixEnd_3660871 : Nat := 4983230072969 + 3 ^ 40 * 3660871 * 2
def baseEnd_3660871 : Nat := 626595479035283853025489

theorem tailTrace_3660871 : CollatzResearch.WordTrace tailWord_3660871 prefixEnd_3660871 626595479035283853025489 := by
  unfold tailWord_3660871
  simp only [CollatzResearch.WordTrace]
  refine ⟨133522934720297068835046467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89015289813531379223364311 133522934720297068835046467)
  ·
    refine ⟨200284402080445603252569701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133522934720297068835046467 200284402080445603252569701)
    ·
      refine ⟨37553325390083550609856819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200284402080445603252569701 37553325390083550609856819)
      ·
        refine ⟨56329988085125325914785229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37553325390083550609856819 56329988085125325914785229)
        ·
          refine ⟨21123745531921997218044461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56329988085125325914785229 21123745531921997218044461)
          ·
            refine ⟨7921404574470748956766673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21123745531921997218044461 7921404574470748956766673)
            ·
              refine ⟨5941053430853061717575005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7921404574470748956766673 5941053430853061717575005)
              ·
                refine ⟨2227895036569898144090627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5941053430853061717575005 2227895036569898144090627)
                ·
                  refine ⟨3341842554854847216135941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227895036569898144090627 3341842554854847216135941)
                  ·
                    refine ⟨626595479035283853025489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3341842554854847216135941 626595479035283853025489)
                    ·
                      rfl

theorem cell23_3660871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_3660871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660871 prefixEnd_3660871 := by exact prefixLift 3660871
  have htrace : WordTrace (prefixWord ++ tailWord_3660871) baseStart_3660871 baseEnd_3660871 := by
    simpa [prefixWord, tailWord_3660871, baseEnd_3660871] using wordTrace_append hprefix tailTrace_3660871
  have hstable : (prefixWord ++ tailWord_3660871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660871).length < 2 ^ (prefixWord ++ tailWord_3660871).sum := by decide
  have hdescent : baseEnd_3660871 < baseStart_3660871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660890 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_3660890 : Nat := 118140960795 + 3660890 * 2 ^ 59
def prefixEnd_3660890 : Nat := 4983230072969 + 3 ^ 40 * 3660890 * 2
def baseEnd_3660890 : Nat := 1879796193238286984738879

theorem tailTrace_3660890 : CollatzResearch.WordTrace tailWord_3660890 prefixEnd_3660890 1879796193238286984738879 := by
  unfold tailWord_3660890
  simp only [CollatzResearch.WordTrace]
  refine ⟨33380906926807058769997031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89015751804818823386658749 33380906926807058769997031)
  ·
    refine ⟨50071360390210588154995547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33380906926807058769997031 50071360390210588154995547)
    ·
      refine ⟨75107040585315882232493321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50071360390210588154995547 75107040585315882232493321)
      ·
        refine ⟨56330280438986911674369991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75107040585315882232493321 56330280438986911674369991)
        ·
          refine ⟨84495420658480367511554987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56330280438986911674369991 84495420658480367511554987)
          ·
            refine ⟨126743130987720551267332481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84495420658480367511554987 126743130987720551267332481)
            ·
              refine ⟨95057348240790413450499361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126743130987720551267332481 95057348240790413450499361)
              ·
                refine ⟨71293011180592810087874521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95057348240790413450499361 71293011180592810087874521)
                ·
                  refine ⟨53469758385444607565905891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71293011180592810087874521 53469758385444607565905891)
                  ·
                    refine ⟨80204637578166911348858837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53469758385444607565905891 80204637578166911348858837)
                    ·
                      refine ⟨1879796193238286984738879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80204637578166911348858837 1879796193238286984738879)
                      ·
                        rfl

theorem cell23_3660890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_3660890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660890 prefixEnd_3660890 := by exact prefixLift 3660890
  have htrace : WordTrace (prefixWord ++ tailWord_3660890) baseStart_3660890 baseEnd_3660890 := by
    simpa [prefixWord, tailWord_3660890, baseEnd_3660890] using wordTrace_append hprefix tailTrace_3660890
  have hstable : (prefixWord ++ tailWord_3660890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660890).length < 2 ^ (prefixWord ++ tailWord_3660890).sum := by decide
  have hdescent : baseEnd_3660890 < baseStart_3660890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660914 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_3660914 : Nat := 118140960795 + 3660914 * 2 ^ 59
def prefixEnd_3660914 : Nat := 4983230072969 + 3 ^ 40 * 3660914 * 2
def baseEnd_3660914 : Nat := 626602838924664963612923

theorem tailTrace_3660914 : CollatzResearch.WordTrace tailWord_3660914 prefixEnd_3660914 626602838924664963612923 := by
  unfold tailWord_3660914
  simp only [CollatzResearch.WordTrace]
  refine ⟨33381125764785321794715449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89016335372760858119241197 33381125764785321794715449)
  ·
    refine ⟨25035844323588991346036587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33381125764785321794715449 25035844323588991346036587)
    ·
      refine ⟨37553766485383487019054881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25035844323588991346036587 37553766485383487019054881)
      ·
        refine ⟨28165324864037615264291161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37553766485383487019054881 28165324864037615264291161)
        ·
          refine ⟨21123993648028211448218371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28165324864037615264291161 21123993648028211448218371)
          ·
            refine ⟨31685990472042317172327557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21123993648028211448218371 31685990472042317172327557)
            ·
              refine ⟨5941123213507934469811417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31685990472042317172327557 5941123213507934469811417)
              ·
                refine ⟨4455842410130950852358563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941123213507934469811417 4455842410130950852358563)
                ·
                  refine ⟨6683763615196426278537845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4455842410130950852358563 6683763615196426278537845)
                  ·
                    refine ⟨626602838924664963612923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6683763615196426278537845 626602838924664963612923)
                    ·
                      rfl

theorem cell23_3660914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_3660914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660914 prefixEnd_3660914 := by exact prefixLift 3660914
  have htrace : WordTrace (prefixWord ++ tailWord_3660914) baseStart_3660914 baseEnd_3660914 := by
    simpa [prefixWord, tailWord_3660914, baseEnd_3660914] using wordTrace_append hprefix tailTrace_3660914
  have hstable : (prefixWord ++ tailWord_3660914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660914).length < 2 ^ (prefixWord ++ tailWord_3660914).sum := by decide
  have hdescent : baseEnd_3660914 < baseStart_3660914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660937 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_3660937 : Nat := 118140960795 + 3660937 * 2 ^ 59
def prefixEnd_3660937 : Nat := 4983230072969 + 3 ^ 40 * 3660937 * 2
def baseEnd_3660937 : Nat := 1879820326829048300851163

theorem tailTrace_3660937 : CollatzResearch.WordTrace tailWord_3660937 prefixEnd_3660937 1879820326829048300851163 := by
  unfold tailWord_3660937
  simp only [CollatzResearch.WordTrace]
  refine ⟨133525341938057962106949065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89016894625371974737966043 133525341938057962106949065)
  ·
    refine ⟨100144006453543471580211799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133525341938057962106949065 100144006453543471580211799)
    ·
      refine ⟨150216009680315207370317699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100144006453543471580211799 150216009680315207370317699)
      ·
        refine ⟨225324014520472811055476549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150216009680315207370317699 225324014520472811055476549)
        ·
          refine ⟨42248252722588652072901853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225324014520472811055476549 42248252722588652072901853)
          ·
            refine ⟨15843094770970744527338195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42248252722588652072901853 15843094770970744527338195)
            ·
              refine ⟨23764642156456116791007293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15843094770970744527338195 23764642156456116791007293)
              ·
                refine ⟨8911740808671043796627735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23764642156456116791007293 8911740808671043796627735)
                ·
                  refine ⟨13367611213006565694941603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8911740808671043796627735 13367611213006565694941603)
                  ·
                    refine ⟨20051416819509848542412405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13367611213006565694941603 20051416819509848542412405)
                    ·
                      refine ⟨1879820326829048300851163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20051416819509848542412405 1879820326829048300851163)
                      ·
                        rfl

theorem cell23_3660937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_3660937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660937 prefixEnd_3660937 := by exact prefixLift 3660937
  have htrace : WordTrace (prefixWord ++ tailWord_3660937) baseStart_3660937 baseEnd_3660937 := by
    simpa [prefixWord, tailWord_3660937, baseEnd_3660937] using wordTrace_append hprefix tailTrace_3660937
  have hstable : (prefixWord ++ tailWord_3660937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660937).length < 2 ^ (prefixWord ++ tailWord_3660937).sum := by decide
  have hdescent : baseEnd_3660937 < baseStart_3660937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660954 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3660954 : Nat := 118140960795 + 3660954 * 2 ^ 59
def prefixEnd_3660954 : Nat := 4983230072969 + 3 ^ 40 * 3660954 * 2
def baseEnd_3660954 : Nat := 1879829056000174734338585

theorem tailTrace_3660954 : CollatzResearch.WordTrace tailWord_3660954 prefixEnd_3660954 1879829056000174734338585 := by
  unfold tailWord_3660954
  simp only [CollatzResearch.WordTrace]
  refine ⟨33381490494749093502579479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89017307985997582673545277 33381490494749093502579479)
  ·
    refine ⟨50072235742123640253869219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33381490494749093502579479 50072235742123640253869219)
    ·
      refine ⟨75108353613185460380803829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50072235742123640253869219 75108353613185460380803829)
      ·
        refine ⟨7041408151236136910700359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75108353613185460380803829 7041408151236136910700359)
        ·
          refine ⟨10562112226854205366050539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7041408151236136910700359 10562112226854205366050539)
          ·
            refine ⟨15843168340281308049075809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10562112226854205366050539 15843168340281308049075809)
            ·
              refine ⟨11882376255210981036806857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15843168340281308049075809 11882376255210981036806857)
              ·
                refine ⟨8911782191408235777605143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11882376255210981036806857 8911782191408235777605143)
                ·
                  refine ⟨13367673287112353666407715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8911782191408235777605143 13367673287112353666407715)
                  ·
                    refine ⟨20051509930668530499611573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13367673287112353666407715 20051509930668530499611573)
                    ·
                      refine ⟨1879829056000174734338585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20051509930668530499611573 1879829056000174734338585)
                      ·
                        rfl

theorem cell23_3660954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3660954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660954 prefixEnd_3660954 := by exact prefixLift 3660954
  have htrace : WordTrace (prefixWord ++ tailWord_3660954) baseStart_3660954 baseEnd_3660954 := by
    simpa [prefixWord, tailWord_3660954, baseEnd_3660954] using wordTrace_append hprefix tailTrace_3660954
  have hstable : (prefixWord ++ tailWord_3660954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660954).length < 2 ^ (prefixWord ++ tailWord_3660954).sum := by decide
  have hdescent : baseEnd_3660954 < baseStart_3660954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660957 : List Nat := [1, 4, 2, 1, 1, 2, 4, 8]
def baseStart_3660957 : Nat := 118140960795 + 3660957 * 2 ^ 59
def prefixEnd_3660957 : Nat := 4983230072969 + 3 ^ 40 * 3660957 * 2
def baseEnd_3660957 : Nat := 69623355423782897133373

theorem tailTrace_3660957 : CollatzResearch.WordTrace tailWord_3660957 prefixEnd_3660957 69623355423782897133373 := by
  unfold tailWord_3660957
  simp only [CollatzResearch.WordTrace]
  refine ⟨133526071397985505522677125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89017380931990337015118083 133526071397985505522677125)
  ·
    refine ⟨25036138387122282285501961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133526071397985505522677125 25036138387122282285501961)
    ·
      refine ⟨18777103790341711714126471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25036138387122282285501961 18777103790341711714126471)
      ·
        refine ⟨28165655685512567571189707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18777103790341711714126471 28165655685512567571189707)
        ·
          refine ⟨42248483528268851356784561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28165655685512567571189707 42248483528268851356784561)
          ·
            refine ⟨31686362646201638517588421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42248483528268851356784561 31686362646201638517588421)
            ·
              refine ⟨5941192996162807222047829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31686362646201638517588421 5941192996162807222047829)
              ·
                refine ⟨69623355423782897133373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5941192996162807222047829 69623355423782897133373)
                ·
                  rfl

theorem cell23_3660957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 8].length) (baseStart_3660957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660957 prefixEnd_3660957 := by exact prefixLift 3660957
  have htrace : WordTrace (prefixWord ++ tailWord_3660957) baseStart_3660957 baseEnd_3660957 := by
    simpa [prefixWord, tailWord_3660957, baseEnd_3660957] using wordTrace_append hprefix tailTrace_3660957
  have hstable : (prefixWord ++ tailWord_3660957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660957).length < 2 ^ (prefixWord ++ tailWord_3660957).sum := by decide
  have hdescent : baseEnd_3660957 < baseStart_3660957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660984 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 4, 1, 3]
def baseStart_3660984 : Nat := 118140960795 + 3660984 * 2 ^ 59
def prefixEnd_3660984 : Nat := 4983230072969 + 3 ^ 40 * 3660984 * 2
def baseEnd_3660984 : Nat := 1879844460419809616963447

theorem tailTrace_3660984 : CollatzResearch.WordTrace tailWord_3660984 prefixEnd_3660984 1879844460419809616963447 := by
  unfold tailWord_3660984
  simp only [CollatzResearch.WordTrace]
  refine ⟨66763528084443844566955003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89018037445925126089273337 66763528084443844566955003)
  ·
    refine ⟨100145292126665766850432505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66763528084443844566955003 100145292126665766850432505)
    ·
      refine ⟨75108969094999325137824379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100145292126665766850432505 75108969094999325137824379)
      ·
        refine ⟨112663453642498987706736569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75108969094999325137824379 112663453642498987706736569)
        ·
          refine ⟨84497590231874240780052427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112663453642498987706736569 84497590231874240780052427)
          ·
            refine ⟨126746385347811361170078641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84497590231874240780052427 126746385347811361170078641)
            ·
              refine ⟨95059789010858520877558981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126746385347811361170078641 95059789010858520877558981)
              ·
                refine ⟨17823710439535972664542309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95059789010858520877558981 17823710439535972664542309)
                ·
                  refine ⟨3341945707412994874601683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17823710439535972664542309 3341945707412994874601683)
                  ·
                    refine ⟨5012918561119492311902525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3341945707412994874601683 5012918561119492311902525)
                    ·
                      refine ⟨1879844460419809616963447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5012918561119492311902525 1879844460419809616963447)
                      ·
                        rfl

theorem cell23_3660984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_3660984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660984 prefixEnd_3660984 := by exact prefixLift 3660984
  have htrace : WordTrace (prefixWord ++ tailWord_3660984) baseStart_3660984 baseEnd_3660984 := by
    simpa [prefixWord, tailWord_3660984, baseEnd_3660984] using wordTrace_append hprefix tailTrace_3660984
  have hstable : (prefixWord ++ tailWord_3660984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660984).length < 2 ^ (prefixWord ++ tailWord_3660984).sum := by decide
  have hdescent : baseEnd_3660984 < baseStart_3660984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660988 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_3660988 : Nat := 118140960795 + 3660988 * 2 ^ 59
def prefixEnd_3660988 : Nat := 4983230072969 + 3 ^ 40 * 3660988 * 2
def baseEnd_3660988 : Nat := 1879846514342427601313429

theorem tailTrace_3660988 : CollatzResearch.WordTrace tailWord_3660988 prefixEnd_3660988 1879846514342427601313429 := by
  unfold tailWord_3660988
  simp only [CollatzResearch.WordTrace]
  refine ⟨66763601030436598908527809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89018134707248798544703745 66763601030436598908527809)
  ·
    refine ⟨50072700772827449181395857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66763601030436598908527809 50072700772827449181395857)
    ·
      refine ⟨37554525579620586886046893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50072700772827449181395857 37554525579620586886046893)
      ·
        refine ⟨14082947092357720082267585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37554525579620586886046893 14082947092357720082267585)
        ·
          refine ⟨10562210319268290061700689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14082947092357720082267585 10562210319268290061700689)
          ·
            refine ⟨7921657739451217546275517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10562210319268290061700689 7921657739451217546275517)
            ·
              refine ⟨2970621652294206579853319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7921657739451217546275517 2970621652294206579853319)
              ·
                refine ⟨4455932478441309869779979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970621652294206579853319 4455932478441309869779979)
                ·
                  refine ⟨6683898717661964804669969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4455932478441309869779979 6683898717661964804669969)
                  ·
                    refine ⟨5012924038246473603502477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6683898717661964804669969 5012924038246473603502477)
                    ·
                      refine ⟨1879846514342427601313429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5012924038246473603502477 1879846514342427601313429)
                      ·
                        rfl

theorem cell23_3660988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_3660988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660988 prefixEnd_3660988 := by exact prefixLift 3660988
  have htrace : WordTrace (prefixWord ++ tailWord_3660988) baseStart_3660988 baseEnd_3660988 := by
    simpa [prefixWord, tailWord_3660988, baseEnd_3660988] using wordTrace_append hprefix tailTrace_3660988
  have hstable : (prefixWord ++ tailWord_3660988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660988).length < 2 ^ (prefixWord ++ tailWord_3660988).sum := by decide
  have hdescent : baseEnd_3660988 < baseStart_3660988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661002 : List Nat := [3, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2]
def baseStart_3661002 : Nat := 118140960795 + 3661002 * 2 ^ 59
def prefixEnd_3661002 : Nat := 4983230072969 + 3 ^ 40 * 3661002 * 2
def baseEnd_3661002 : Nat := 1879853703071590546538365

theorem tailTrace_3661002 : CollatzResearch.WordTrace tailWord_3661002 prefixEnd_3661002 1879853703071590546538365 := by
  unfold tailWord_3661002
  simp only [CollatzResearch.WordTrace]
  refine ⟨33381928170705619552016315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89018475121881652138710173 33381928170705619552016315)
  ·
    refine ⟨50072892256058429328024473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33381928170705619552016315 50072892256058429328024473)
    ·
      refine ⟨37554669192043821996018355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50072892256058429328024473 37554669192043821996018355)
      ·
        refine ⟨56332003788065732994027533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37554669192043821996018355 56332003788065732994027533)
        ·
          refine ⟨21124501420524649872760325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56332003788065732994027533 21124501420524649872760325)
          ·
            refine ⟨3960844016348371851142561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21124501420524649872760325 3960844016348371851142561)
            ·
              refine ⟨2970633012261278888356921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960844016348371851142561 2970633012261278888356921)
              ·
                refine ⟨2227974759195959166267691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970633012261278888356921 2227974759195959166267691)
                ·
                  refine ⟨3341962138793938749401537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227974759195959166267691 3341962138793938749401537)
                  ·
                    refine ⟨2506471604095454062051153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3341962138793938749401537 2506471604095454062051153)
                    ·
                      refine ⟨1879853703071590546538365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506471604095454062051153 1879853703071590546538365)
                      ·
                        rfl

theorem cell23_3661002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_3661002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661002 prefixEnd_3661002 := by exact prefixLift 3661002
  have htrace : WordTrace (prefixWord ++ tailWord_3661002) baseStart_3661002 baseEnd_3661002 := by
    simpa [prefixWord, tailWord_3661002, baseEnd_3661002] using wordTrace_append hprefix tailTrace_3661002
  have hstable : (prefixWord ++ tailWord_3661002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661002).length < 2 ^ (prefixWord ++ tailWord_3661002).sum := by decide
  have hdescent : baseEnd_3661002 < baseStart_3661002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661041 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 4, 2, 2]
def baseStart_3661041 : Nat := 118140960795 + 3661041 * 2 ^ 59
def prefixEnd_3661041 : Nat := 4983230072969 + 3 ^ 40 * 3661041 * 2
def baseEnd_3661041 : Nat := 1879873728817115893950685

theorem tailTrace_3661041 : CollatzResearch.WordTrace tailWord_3661041 prefixEnd_3661041 1879873728817115893950685 := by
  unfold tailWord_3661041
  simp only [CollatzResearch.WordTrace]
  refine ⟨133529135129681187868734977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89019423419787458579156651 133529135129681187868734977)
  ·
    refine ⟨100146851347260890901551233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133529135129681187868734977 100146851347260890901551233)
    ·
      refine ⟨75110138510445668176163425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100146851347260890901551233 75110138510445668176163425)
      ·
        refine ⟨56332603882834251132122569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75110138510445668176163425 56332603882834251132122569)
        ·
          refine ⟨42249452912125688349091927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56332603882834251132122569 42249452912125688349091927)
          ·
            refine ⟨63374179368188532523637891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42249452912125688349091927 63374179368188532523637891)
            ·
              refine ⟨95061269052282798785456837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63374179368188532523637891 95061269052282798785456837)
              ·
                refine ⟨17823987947303024772273157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95061269052282798785456837 17823987947303024772273157)
                ·
                  refine ⟨3341997740119317144801217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17823987947303024772273157 3341997740119317144801217)
                  ·
                    refine ⟨2506498305089487858600913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3341997740119317144801217 2506498305089487858600913)
                    ·
                      refine ⟨1879873728817115893950685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506498305089487858600913 1879873728817115893950685)
                      ·
                        rfl

theorem cell23_3661041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_3661041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661041 prefixEnd_3661041 := by exact prefixLift 3661041
  have htrace : WordTrace (prefixWord ++ tailWord_3661041) baseStart_3661041 baseEnd_3661041 := by
    simpa [prefixWord, tailWord_3661041, baseEnd_3661041] using wordTrace_append hprefix tailTrace_3661041
  have hstable : (prefixWord ++ tailWord_3661041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661041).length < 2 ^ (prefixWord ++ tailWord_3661041).sum := by decide
  have hdescent : baseEnd_3661041 < baseStart_3661041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661098 : List Nat := [3, 1, 4, 2, 1, 1, 3, 3, 5]
def baseStart_3661098 : Nat := 118140960795 + 3661098 * 2 ^ 59
def prefixEnd_3661098 : Nat := 4983230072969 + 3 ^ 40 * 3661098 * 2
def baseEnd_3661098 : Nat := 208878110801602463437547

theorem tailTrace_3661098 : CollatzResearch.WordTrace tailWord_3661098 prefixEnd_3661098 208878110801602463437547 := by
  unfold tailWord_3661098
  simp only [CollatzResearch.WordTrace]
  refine ⟨33382803522618671650889987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89020809393649791069039965 33382803522618671650889987)
  ·
    refine ⟨50074205283928007476334981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33382803522618671650889987 50074205283928007476334981)
    ·
      refine ⟨9388913490736501401812809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50074205283928007476334981 9388913490736501401812809)
      ·
        refine ⟨7041685118052376051359607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9388913490736501401812809 7041685118052376051359607)
        ·
          refine ⟨10562527677078564077039411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7041685118052376051359607 10562527677078564077039411)
          ·
            refine ⟨15843791515617846115559117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10562527677078564077039411 15843791515617846115559117)
            ·
              refine ⟨5941421818356692293334669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15843791515617846115559117 5941421818356692293334669)
              ·
                refine ⟨2228033181883759610000501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5941421818356692293334669 2228033181883759610000501)
                ·
                  refine ⟨208878110801602463437547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2228033181883759610000501 208878110801602463437547)
                  ·
                    rfl

theorem cell23_3661098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_3661098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661098 prefixEnd_3661098 := by exact prefixLift 3661098
  have htrace : WordTrace (prefixWord ++ tailWord_3661098) baseStart_3661098 baseEnd_3661098 := by
    simpa [prefixWord, tailWord_3661098, baseEnd_3661098] using wordTrace_append hprefix tailTrace_3661098
  have hstable : (prefixWord ++ tailWord_3661098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661098).length < 2 ^ (prefixWord ++ tailWord_3661098).sum := by decide
  have hdescent : baseEnd_3661098 < baseStart_3661098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661121 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3661121 : Nat := 118140960795 + 3661121 * 2 ^ 59
def prefixEnd_3661121 : Nat := 4983230072969 + 3 ^ 40 * 3661121 * 2
def baseEnd_3661121 : Nat := 1879914807269475580950317

theorem tailTrace_3661121 : CollatzResearch.WordTrace tailWord_3661121 prefixEnd_3661121 1879914807269475580950317 := by
  unfold tailWord_3661121
  simp only [CollatzResearch.WordTrace]
  refine ⟨133532052969391361531647217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89021368646260907687764811 133532052969391361531647217)
  ·
    refine ⟨100149039727043521148735413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133532052969391361531647217 100149039727043521148735413)
    ·
      refine ⟨9388972474410330107693945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100149039727043521148735413 9388972474410330107693945)
      ·
        refine ⟨7041729355807747580770459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9388972474410330107693945 7041729355807747580770459)
        ·
          refine ⟨10562594033711621371155689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7041729355807747580770459 10562594033711621371155689)
          ·
            refine ⟨7921945525283716028366767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10562594033711621371155689 7921945525283716028366767)
            ·
              refine ⟨11882918287925574042550151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7921945525283716028366767 11882918287925574042550151)
              ·
                refine ⟨17824377431888361063825227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11882918287925574042550151 17824377431888361063825227)
                ·
                  refine ⟨26736566147832541595737841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17824377431888361063825227 26736566147832541595737841)
                  ·
                    refine ⟨20052424610874406196803381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26736566147832541595737841 20052424610874406196803381)
                    ·
                      refine ⟨1879914807269475580950317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20052424610874406196803381 1879914807269475580950317)
                      ·
                        rfl

theorem cell23_3661121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3661121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661121 prefixEnd_3661121 := by exact prefixLift 3661121
  have htrace : WordTrace (prefixWord ++ tailWord_3661121) baseStart_3661121 baseEnd_3661121 := by
    simpa [prefixWord, tailWord_3661121, baseEnd_3661121] using wordTrace_append hprefix tailTrace_3661121
  have hstable : (prefixWord ++ tailWord_3661121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661121).length < 2 ^ (prefixWord ++ tailWord_3661121).sum := by decide
  have hdescent : baseEnd_3661121 < baseStart_3661121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661182 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3661182 : Nat := 118140960795 + 3661182 * 2 ^ 59
def prefixEnd_3661182 : Nat := 4983230072969 + 3 ^ 40 * 3661182 * 2
def baseEnd_3661182 : Nat := 1879946129589399842287537

theorem tailTrace_3661182 : CollatzResearch.WordTrace tailWord_3661182 prefixEnd_3661182 1879946129589399842287537 := by
  unfold tailWord_3661182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16691784727771296118702225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89022851881446912633078533 16691784727771296118702225)
  ·
    refine ⟨12518838545828472089026669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16691784727771296118702225 12518838545828472089026669)
    ·
      refine ⟨4694564454685677033385001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12518838545828472089026669 4694564454685677033385001)
      ·
        refine ⟨3520923341014257775038751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4694564454685677033385001 3520923341014257775038751)
        ·
          refine ⟨5281385011521386662558127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520923341014257775038751 5281385011521386662558127)
          ·
            refine ⟨7922077517282079993837191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281385011521386662558127 7922077517282079993837191)
            ·
              refine ⟨11883116275923119990755787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922077517282079993837191 11883116275923119990755787)
              ·
                refine ⟨17824674413884679986133681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11883116275923119990755787 17824674413884679986133681)
                ·
                  refine ⟨13368505810413509989600261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17824674413884679986133681 13368505810413509989600261)
                  ·
                    refine ⟨2506594839452533123050049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13368505810413509989600261 2506594839452533123050049)
                    ·
                      refine ⟨1879946129589399842287537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506594839452533123050049 1879946129589399842287537)
                      ·
                        rfl

theorem cell23_3661182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3661182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661182 prefixEnd_3661182 := by exact prefixLift 3661182
  have htrace : WordTrace (prefixWord ++ tailWord_3661182) baseStart_3661182 baseEnd_3661182 := by
    simpa [prefixWord, tailWord_3661182, baseEnd_3661182] using wordTrace_append hprefix tailTrace_3661182
  have hstable : (prefixWord ++ tailWord_3661182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661182).length < 2 ^ (prefixWord ++ tailWord_3661182).sum := by decide
  have hdescent : baseEnd_3661182 < baseStart_3661182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661202 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3661202 : Nat := 118140960795 + 3661202 * 2 ^ 59
def prefixEnd_3661202 : Nat := 4983230072969 + 3 ^ 40 * 3661202 * 2
def baseEnd_3661202 : Nat := 1879956399202489764037445

theorem tailTrace_3661202 : CollatzResearch.WordTrace tailWord_3661202 prefixEnd_3661202 1879956399202489764037445 := by
  unfold tailWord_3661202
  simp only [CollatzResearch.WordTrace]
  refine ⟨33383751820524478091336465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89023338188065274910230573 33383751820524478091336465)
  ·
    refine ⟨25037813865393358568502349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33383751820524478091336465 25037813865393358568502349)
    ·
      refine ⟨9389180199522509463188381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25037813865393358568502349 9389180199522509463188381)
      ·
        refine ⟨3520942574820941048695643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9389180199522509463188381 3520942574820941048695643)
        ·
          refine ⟨5281413862231411573043465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520942574820941048695643 5281413862231411573043465)
          ·
            refine ⟨3961060396673558679782599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5281413862231411573043465 3961060396673558679782599)
            ·
              refine ⟨5941590595010338019673899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961060396673558679782599 5941590595010338019673899)
              ·
                refine ⟨8912385892515507029510849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941590595010338019673899 8912385892515507029510849)
                ·
                  refine ⟨6684289419386630272133137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8912385892515507029510849 6684289419386630272133137)
                  ·
                    refine ⟨5013217064539972704099853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6684289419386630272133137 5013217064539972704099853)
                    ·
                      refine ⟨1879956399202489764037445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5013217064539972704099853 1879956399202489764037445)
                      ·
                        rfl

theorem cell23_3661202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3661202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661202 prefixEnd_3661202 := by exact prefixLift 3661202
  have htrace : WordTrace (prefixWord ++ tailWord_3661202) baseStart_3661202 baseEnd_3661202 := by
    simpa [prefixWord, tailWord_3661202, baseEnd_3661202] using wordTrace_append hprefix tailTrace_3661202
  have hstable : (prefixWord ++ tailWord_3661202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661202).length < 2 ^ (prefixWord ++ tailWord_3661202).sum := by decide
  have hdescent : baseEnd_3661202 < baseStart_3661202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661215 : List Nat := [1, 1, 2, 5, 1, 2, 1, 5, 1, 1, 3]
def baseStart_3661215 : Nat := 118140960795 + 3661215 * 2 ^ 59
def prefixEnd_3661215 : Nat := 4983230072969 + 3 ^ 40 * 3661215 * 2
def baseEnd_3661215 : Nat := 1879963074450998213174885

theorem tailTrace_3661215 : CollatzResearch.WordTrace tailWord_3661215 prefixEnd_3661215 1879963074450998213174885 := by
  unfold tailWord_3661215
  simp only [CollatzResearch.WordTrace]
  refine ⟨133535481431050815585569099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89023654287367210390379399 133535481431050815585569099)
  ·
    refine ⟨200303222146576223378353649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133535481431050815585569099 200303222146576223378353649)
    ·
      refine ⟨150227416609932167533765237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200303222146576223378353649 150227416609932167533765237)
      ·
        refine ⟨14083820307181140706290491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150227416609932167533765237 14083820307181140706290491)
        ·
          refine ⟨21125730460771711059435737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14083820307181140706290491 21125730460771711059435737)
          ·
            refine ⟨15844297845578783294576803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21125730460771711059435737 15844297845578783294576803)
            ·
              refine ⟨23766446768368174941865205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15844297845578783294576803 23766446768368174941865205)
              ·
                refine ⟨2228104384534516400799863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23766446768368174941865205 2228104384534516400799863)
                ·
                  refine ⟨3342156576801774601199795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228104384534516400799863 3342156576801774601199795)
                  ·
                    refine ⟨5013234865202661901799693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3342156576801774601199795 5013234865202661901799693)
                    ·
                      refine ⟨1879963074450998213174885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5013234865202661901799693 1879963074450998213174885)
                      ·
                        rfl

theorem cell23_3661215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_3661215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661215 prefixEnd_3661215 := by exact prefixLift 3661215
  have htrace : WordTrace (prefixWord ++ tailWord_3661215) baseStart_3661215 baseEnd_3661215 := by
    simpa [prefixWord, tailWord_3661215, baseEnd_3661215] using wordTrace_append hprefix tailTrace_3661215
  have hstable : (prefixWord ++ tailWord_3661215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661215).length < 2 ^ (prefixWord ++ tailWord_3661215).sum := by decide
  have hdescent : baseEnd_3661215 < baseStart_3661215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661218 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3661218 : Nat := 118140960795 + 3661218 * 2 ^ 59
def prefixEnd_3661218 : Nat := 4983230072969 + 3 ^ 40 * 3661218 * 2
def baseEnd_3661218 : Nat := 626654871630987233812457

theorem tailTrace_3661218 : CollatzResearch.WordTrace tailWord_3661218 prefixEnd_3661218 626654871630987233812457 := by
  unfold tailWord_3661218
  simp only [CollatzResearch.WordTrace]
  refine ⟨33383897712509986774482077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89023727233359964731952205 33383897712509986774482077)
  ·
    refine ⟨12518961642191245040430779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33383897712509986774482077 12518961642191245040430779)
    ·
      refine ⟨18778442463286867560646169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12518961642191245040430779 18778442463286867560646169)
      ·
        refine ⟨14083831847465150670484627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18778442463286867560646169 14083831847465150670484627)
        ·
          refine ⟨21125747771197726005726941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14083831847465150670484627 21125747771197726005726941)
          ·
            refine ⟨7922155414199147252147603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21125747771197726005726941 7922155414199147252147603)
            ·
              refine ⟨11883233121298720878221405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922155414199147252147603 11883233121298720878221405)
              ·
                refine ⟨4456212420487020329333027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11883233121298720878221405 4456212420487020329333027)
                ·
                  refine ⟨6684318630730530493999541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456212420487020329333027 6684318630730530493999541)
                  ·
                    refine ⟨626654871630987233812457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6684318630730530493999541 626654871630987233812457)
                    ·
                      rfl

theorem cell23_3661218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3661218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661218 prefixEnd_3661218 := by exact prefixLift 3661218
  have htrace : WordTrace (prefixWord ++ tailWord_3661218) baseStart_3661218 baseEnd_3661218 := by
    simpa [prefixWord, tailWord_3661218, baseEnd_3661218] using wordTrace_append hprefix tailTrace_3661218
  have hstable : (prefixWord ++ tailWord_3661218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661218).length < 2 ^ (prefixWord ++ tailWord_3661218).sum := by decide
  have hdescent : baseEnd_3661218 < baseStart_3661218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661251 : List Nat := [1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 4]
def baseStart_3661251 : Nat := 118140960795 + 3661251 * 2 ^ 59
def prefixEnd_3661251 : Nat := 4983230072969 + 3 ^ 40 * 3661251 * 2
def baseEnd_3661251 : Nat := 1879981559754560072324719

theorem tailTrace_3661251 : CollatzResearch.WordTrace tailWord_3661251 prefixEnd_3661251 1879981559754560072324719 := by
  unfold tailWord_3661251
  simp only [CollatzResearch.WordTrace]
  refine ⟨133536794458920393733879607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89024529639280262489253071 133536794458920393733879607)
  ·
    refine ⟨200305191688380590600819411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133536794458920393733879607 200305191688380590600819411)
    ·
      refine ⟨300457787532570885901229117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200305191688380590600819411 300457787532570885901229117)
      ·
        refine ⟨112671670324714082212960919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300457787532570885901229117 112671670324714082212960919)
        ·
          refine ⟨169007505487071123319441379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112671670324714082212960919 169007505487071123319441379)
          ·
            refine ⟨253511258230606684979162069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169007505487071123319441379 253511258230606684979162069)
            ·
              refine ⟨5941670114779844179199111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 253511258230606684979162069 5941670114779844179199111)
              ·
                refine ⟨8912505172169766268798667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941670114779844179199111 8912505172169766268798667)
                ·
                  refine ⟨13368757758254649403198001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8912505172169766268798667 13368757758254649403198001)
                  ·
                    refine ⟨10026568318690987052398501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13368757758254649403198001 10026568318690987052398501)
                    ·
                      refine ⟨1879981559754560072324719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10026568318690987052398501 1879981559754560072324719)
                      ·
                        rfl

theorem cell23_3661251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_3661251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661251 prefixEnd_3661251 := by exact prefixLift 3661251
  have htrace : WordTrace (prefixWord ++ tailWord_3661251) baseStart_3661251 baseEnd_3661251 := by
    simpa [prefixWord, tailWord_3661251, baseEnd_3661251] using wordTrace_append hprefix tailTrace_3661251
  have hstable : (prefixWord ++ tailWord_3661251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661251).length < 2 ^ (prefixWord ++ tailWord_3661251).sum := by decide
  have hdescent : baseEnd_3661251 < baseStart_3661251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661258 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3]
def baseStart_3661258 : Nat := 118140960795 + 3661258 * 2 ^ 59
def prefixEnd_3661258 : Nat := 4983230072969 + 3 ^ 40 * 3661258 * 2
def baseEnd_3661258 : Nat := 1879985154119141544937187

theorem tailTrace_3661258 : CollatzResearch.WordTrace tailWord_3661258 prefixEnd_3661258 1879985154119141544937187 := by
  unfold tailWord_3661258
  simp only [CollatzResearch.WordTrace]
  refine ⟨33384262442473758482346107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89024699846596689286256285 33384262442473758482346107)
  ·
    refine ⟨50076393663710637723519161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33384262442473758482346107 50076393663710637723519161)
    ·
      refine ⟨37557295247782978292639371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50076393663710637723519161 37557295247782978292639371)
      ·
        refine ⟨56335942871674467438959057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37557295247782978292639371 56335942871674467438959057)
        ·
          refine ⟨42251957153755850579219293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56335942871674467438959057 42251957153755850579219293)
          ·
            refine ⟨15844483932658443967207235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42251957153755850579219293 15844483932658443967207235)
            ·
              refine ⟨23766725898987665950810853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15844483932658443967207235 23766725898987665950810853)
              ·
                refine ⟨4456261106060187365777035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23766725898987665950810853 4456261106060187365777035)
                ·
                  refine ⟨6684391659090281048665553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456261106060187365777035 6684391659090281048665553)
                  ·
                    refine ⟨5013293744317710786499165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6684391659090281048665553 5013293744317710786499165)
                    ·
                      refine ⟨1879985154119141544937187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5013293744317710786499165 1879985154119141544937187)
                      ·
                        rfl

theorem cell23_3661258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_3661258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661258 prefixEnd_3661258 := by exact prefixLift 3661258
  have htrace : WordTrace (prefixWord ++ tailWord_3661258) baseStart_3661258 baseEnd_3661258 := by
    simpa [prefixWord, tailWord_3661258, baseEnd_3661258] using wordTrace_append hprefix tailTrace_3661258
  have hstable : (prefixWord ++ tailWord_3661258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661258).length < 2 ^ (prefixWord ++ tailWord_3661258).sum := by decide
  have hdescent : baseEnd_3661258 < baseStart_3661258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661271 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_3661271 : Nat := 118140960795 + 3661271 * 2 ^ 59
def prefixEnd_3661271 : Nat := 4983230072969 + 3 ^ 40 * 3661271 * 2
def baseEnd_3661271 : Nat := 1879991829367649994074627

theorem tailTrace_3661271 : CollatzResearch.WordTrace tailWord_3661271 prefixEnd_3661271 1879991829367649994074627 := by
  unfold tailWord_3661271
  simp only [CollatzResearch.WordTrace]
  refine ⟨133537523918847937149607667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89025015945898624766405111 133537523918847937149607667)
  ·
    refine ⟨200306285878271905724411501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133537523918847937149607667 200306285878271905724411501)
    ·
      refine ⟨75114857204351964646654313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200306285878271905724411501 75114857204351964646654313)
      ·
        refine ⟨56336142903263973484990735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75114857204351964646654313 56336142903263973484990735)
        ·
          refine ⟨84504214354895960227486103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56336142903263973484990735 84504214354895960227486103)
          ·
            refine ⟨126756321532343940341229155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84504214354895960227486103 126756321532343940341229155)
            ·
              refine ⟨190134482298515910511843733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126756321532343940341229155 190134482298515910511843733)
              ·
                refine ⟨8912553857742933305242675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190134482298515910511843733 8912553857742933305242675)
                ·
                  refine ⟨13368830786614399957864013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8912553857742933305242675 13368830786614399957864013)
                  ·
                    refine ⟨5013311544980399984199005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13368830786614399957864013 5013311544980399984199005)
                    ·
                      refine ⟨1879991829367649994074627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5013311544980399984199005 1879991829367649994074627)
                      ·
                        rfl

theorem cell23_3661271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_3661271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661271 prefixEnd_3661271 := by exact prefixLift 3661271
  have htrace : WordTrace (prefixWord ++ tailWord_3661271) baseStart_3661271 baseEnd_3661271 := by
    simpa [prefixWord, tailWord_3661271, baseEnd_3661271] using wordTrace_append hprefix tailTrace_3661271
  have hstable : (prefixWord ++ tailWord_3661271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661271).length < 2 ^ (prefixWord ++ tailWord_3661271).sum := by decide
  have hdescent : baseEnd_3661271 < baseStart_3661271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661272 : List Nat := [2, 1, 2, 2, 2, 1, 5, 3, 1, 2, 2]
def baseStart_3661272 : Nat := 118140960795 + 3661272 * 2 ^ 59
def prefixEnd_3661272 : Nat := 4983230072969 + 3 ^ 40 * 3661272 * 2
def baseEnd_3661272 : Nat := 1879992342848304490162123

theorem tailTrace_3661272 : CollatzResearch.WordTrace tailWord_3661272 prefixEnd_3661272 1879992342848304490162123 := by
  unfold tailWord_3661272
  simp only [CollatzResearch.WordTrace]
  refine ⟨66768780195922157160197035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89025040261229542880262713 66768780195922157160197035)
  ·
    refine ⟨100153170293883235740295553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66768780195922157160197035 100153170293883235740295553)
    ·
      refine ⟨75114877720412426805221665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100153170293883235740295553 75114877720412426805221665)
      ·
        refine ⟨56336158290309320103916249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75114877720412426805221665 56336158290309320103916249)
        ·
          refine ⟨42252118717731990077937187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56336158290309320103916249 42252118717731990077937187)
          ·
            refine ⟨63378178076597985116905781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42252118717731990077937187 63378178076597985116905781)
            ·
              refine ⟨5941704194681061104709917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63378178076597985116905781 5941704194681061104709917)
              ·
                refine ⟨2228139073005397914266219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5941704194681061104709917 2228139073005397914266219)
                ·
                  refine ⟨3342208609508096871399329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228139073005397914266219 3342208609508096871399329)
                  ·
                    refine ⟨2506656457131072653549497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3342208609508096871399329 2506656457131072653549497)
                    ·
                      refine ⟨1879992342848304490162123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506656457131072653549497 1879992342848304490162123)
                      ·
                        rfl

theorem cell23_3661272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_3661272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661272 prefixEnd_3661272 := by exact prefixLift 3661272
  have htrace : WordTrace (prefixWord ++ tailWord_3661272) baseStart_3661272 baseEnd_3661272 := by
    simpa [prefixWord, tailWord_3661272, baseEnd_3661272] using wordTrace_append hprefix tailTrace_3661272
  have hstable : (prefixWord ++ tailWord_3661272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661272).length < 2 ^ (prefixWord ++ tailWord_3661272).sum := by decide
  have hdescent : baseEnd_3661272 < baseStart_3661272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661288 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3661288 : Nat := 118140960795 + 3661288 * 2 ^ 59
def prefixEnd_3661288 : Nat := 4983230072969 + 3 ^ 40 * 3661288 * 2
def baseEnd_3661288 : Nat := 1880000558538776427562049

theorem tailTrace_3661288 : CollatzResearch.WordTrace tailWord_3661288 prefixEnd_3661288 1880000558538776427562049 := by
  unfold tailWord_3661288
  simp only [CollatzResearch.WordTrace]
  refine ⟨66769071979893174526488259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89025429306524232701984345 66769071979893174526488259)
  ·
    refine ⟨100153607969839761789732389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66769071979893174526488259 100153607969839761789732389)
    ·
      refine ⟨18778801494344955335574823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100153607969839761789732389 18778801494344955335574823)
      ·
        refine ⟨28168202241517433003362235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18778801494344955335574823 28168202241517433003362235)
        ·
          refine ⟨42252303362276149505043353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28168202241517433003362235 42252303362276149505043353)
          ·
            refine ⟨31689227521707112128782515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42252303362276149505043353 31689227521707112128782515)
            ·
              refine ⟨47533841282560668193173773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31689227521707112128782515 47533841282560668193173773)
              ·
                refine ⟨17825190480960250572440165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47533841282560668193173773 17825190480960250572440165)
                ·
                  refine ⟨3342223215180046982332531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17825190480960250572440165 3342223215180046982332531)
                  ·
                    refine ⟨5013334822770070473498797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3342223215180046982332531 5013334822770070473498797)
                    ·
                      refine ⟨1880000558538776427562049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5013334822770070473498797 1880000558538776427562049)
                      ·
                        rfl

theorem cell23_3661288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3661288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661288 prefixEnd_3661288 := by exact prefixLift 3661288
  have htrace : WordTrace (prefixWord ++ tailWord_3661288) baseStart_3661288 baseEnd_3661288 := by
    simpa [prefixWord, tailWord_3661288, baseEnd_3661288] using wordTrace_append hprefix tailTrace_3661288
  have hstable : (prefixWord ++ tailWord_3661288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661288).length < 2 ^ (prefixWord ++ tailWord_3661288).sum := by decide
  have hdescent : baseEnd_3661288 < baseStart_3661288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661331 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 5]
def baseStart_3661331 : Nat := 118140960795 + 3661331 * 2 ^ 59
def prefixEnd_3661331 : Nat := 4983230072969 + 3 ^ 40 * 3661331 * 2
def baseEnd_3661331 : Nat := 1880022638206919759324351

theorem tailTrace_3661331 : CollatzResearch.WordTrace tailWord_3661331 prefixEnd_3661331 1880022638206919759324351 := by
  unfold tailWord_3661331
  simp only [CollatzResearch.WordTrace]
  refine ⟨133539712298630567396791847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89026474865753711597861231 133539712298630567396791847)
  ·
    refine ⟨200309568447945851095187771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133539712298630567396791847 200309568447945851095187771)
    ·
      refine ⟨300464352671918776642781657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200309568447945851095187771 300464352671918776642781657)
      ·
        refine ⟨225348264503939082482086243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300464352671918776642781657 225348264503939082482086243)
        ·
          refine ⟨338022396755908623723129365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225348264503939082482086243 338022396755908623723129365)
          ·
            refine ⟨15844799847933216737021689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 338022396755908623723129365 15844799847933216737021689)
            ·
              refine ⟨11883599885949912552766267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15844799847933216737021689 11883599885949912552766267)
              ·
                refine ⟨17825399828924868829149401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11883599885949912552766267 17825399828924868829149401)
                ·
                  refine ⟨13369049871693651621862051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17825399828924868829149401 13369049871693651621862051)
                  ·
                    refine ⟨20053574807540477432793077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13369049871693651621862051 20053574807540477432793077)
                    ·
                      refine ⟨1880022638206919759324351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20053574807540477432793077 1880022638206919759324351)
                      ·
                        rfl

theorem cell23_3661331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_3661331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661331 prefixEnd_3661331 := by exact prefixLift 3661331
  have htrace : WordTrace (prefixWord ++ tailWord_3661331) baseStart_3661331 baseEnd_3661331 := by
    simpa [prefixWord, tailWord_3661331, baseEnd_3661331] using wordTrace_append hprefix tailTrace_3661331
  have hstable : (prefixWord ++ tailWord_3661331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661331).length < 2 ^ (prefixWord ++ tailWord_3661331).sum := by decide
  have hdescent : baseEnd_3661331 < baseStart_3661331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661358 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3661358 : Nat := 118140960795 + 3661358 * 2 ^ 59
def prefixEnd_3661358 : Nat := 4983230072969 + 3 ^ 40 * 3661358 * 2
def baseEnd_3661358 : Nat := 1880036502184591153686727

theorem tailTrace_3661358 : CollatzResearch.WordTrace tailWord_3661358 prefixEnd_3661358 1880036502184591153686727 := by
  unfold tailWord_3661358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16692587133691593876003091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89027131379688500672016485 16692587133691593876003091)
  ·
    refine ⟨25038880700537390814004637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16692587133691593876003091 25038880700537390814004637)
    ·
      refine ⟨9389580262701521555251739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25038880700537390814004637 9389580262701521555251739)
      ·
        refine ⟨14084370394052282332877609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9389580262701521555251739 14084370394052282332877609)
        ·
          refine ⟨10563277795539211749658207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14084370394052282332877609 10563277795539211749658207)
          ·
            refine ⟨15844916693308817624487311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10563277795539211749658207 15844916693308817624487311)
            ·
              refine ⟨23767375039963226436730967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15844916693308817624487311 23767375039963226436730967)
              ·
                refine ⟨35651062559944839655096451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23767375039963226436730967 35651062559944839655096451)
                ·
                  refine ⟨53476593839917259482644677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35651062559944839655096451 53476593839917259482644677)
                  ·
                    refine ⟨10026861344984486152995877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53476593839917259482644677 10026861344984486152995877)
                    ·
                      refine ⟨1880036502184591153686727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10026861344984486152995877 1880036502184591153686727)
                      ·
                        rfl

theorem cell23_3661358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3661358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661358 prefixEnd_3661358 := by exact prefixLift 3661358
  have htrace : WordTrace (prefixWord ++ tailWord_3661358) baseStart_3661358 baseEnd_3661358 := by
    simpa [prefixWord, tailWord_3661358, baseEnd_3661358] using wordTrace_append hprefix tailTrace_3661358
  have hstable : (prefixWord ++ tailWord_3661358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661358).length < 2 ^ (prefixWord ++ tailWord_3661358).sum := by decide
  have hdescent : baseEnd_3661358 < baseStart_3661358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661381 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_3661381 : Nat := 118140960795 + 3661381 * 2 ^ 59
def prefixEnd_3661381 : Nat := 4983230072969 + 3 ^ 40 * 3661381 * 2
def baseEnd_3661381 : Nat := 626682770746548187899707

theorem tailTrace_3661381 : CollatzResearch.WordTrace tailWord_3661381 prefixEnd_3661381 626682770746548187899707 := by
  unfold tailWord_3661381
  simp only [CollatzResearch.WordTrace]
  refine ⟨133541535948449425936111997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89027690632299617290741331 133541535948449425936111997)
  ·
    refine ⟨50078075980668534726041999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133541535948449425936111997 50078075980668534726041999)
    ·
      refine ⟨75117113971002802089062999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50078075980668534726041999 75117113971002802089062999)
      ·
        refine ⟨112675670956504203133594499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75117113971002802089062999 112675670956504203133594499)
        ·
          refine ⟨169013506434756304700391749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112675670956504203133594499 169013506434756304700391749)
          ·
            refine ⟨31690032456516807131323453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169013506434756304700391749 31690032456516807131323453)
            ·
              refine ⟨11883762171193802674246295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31690032456516807131323453 11883762171193802674246295)
              ·
                refine ⟨17825643256790704011369443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11883762171193802674246295 17825643256790704011369443)
                ·
                  refine ⟨26738464885186056017054165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17825643256790704011369443 26738464885186056017054165)
                  ·
                    refine ⟨626682770746548187899707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26738464885186056017054165 626682770746548187899707)
                    ·
                      rfl

theorem cell23_3661381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_3661381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661381 prefixEnd_3661381 := by exact prefixLift 3661381
  have htrace : WordTrace (prefixWord ++ tailWord_3661381) baseStart_3661381 baseEnd_3661381 := by
    simpa [prefixWord, tailWord_3661381, baseEnd_3661381] using wordTrace_append hprefix tailTrace_3661381
  have hstable : (prefixWord ++ tailWord_3661381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661381).length < 2 ^ (prefixWord ++ tailWord_3661381).sum := by decide
  have hdescent : baseEnd_3661381 < baseStart_3661381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661418 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3661418 : Nat := 118140960795 + 3661418 * 2 ^ 59
def prefixEnd_3661418 : Nat := 4983230072969 + 3 ^ 40 * 3661418 * 2
def baseEnd_3661418 : Nat := 1880067311023860918936451

theorem tailTrace_3661418 : CollatzResearch.WordTrace tailWord_3661418 prefixEnd_3661418 1880067311023860918936451 := by
  unfold tailWord_3661418
  simp only [CollatzResearch.WordTrace]
  refine ⟨33385721362328845313802227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89028590299543587503472605 33385721362328845313802227)
  ·
    refine ⟨50078582043493267970703341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33385721362328845313802227 50078582043493267970703341)
    ·
      refine ⟨18779468266309975489013753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50078582043493267970703341 18779468266309975489013753)
      ·
        refine ⟨14084601199732481616760315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18779468266309975489013753 14084601199732481616760315)
        ·
          refine ⟨21126901799598722425140473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14084601199732481616760315 21126901799598722425140473)
          ·
            refine ⟨15845176349699041818855355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21126901799598722425140473 15845176349699041818855355)
            ·
              refine ⟨23767764524548562728283033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15845176349699041818855355 23767764524548562728283033)
              ·
                refine ⟨17825823393411422046212275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23767764524548562728283033 17825823393411422046212275)
                ·
                  refine ⟨26738735090117133069318413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17825823393411422046212275 26738735090117133069318413)
                  ·
                    refine ⟨10027025658793924900994405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26738735090117133069318413 10027025658793924900994405)
                    ·
                      refine ⟨1880067311023860918936451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10027025658793924900994405 1880067311023860918936451)
                      ·
                        rfl

theorem cell23_3661418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3661418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661418 prefixEnd_3661418 := by exact prefixLift 3661418
  have htrace : WordTrace (prefixWord ++ tailWord_3661418) baseStart_3661418 baseEnd_3661418 := by
    simpa [prefixWord, tailWord_3661418, baseEnd_3661418] using wordTrace_append hprefix tailTrace_3661418
  have hstable : (prefixWord ++ tailWord_3661418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661418).length < 2 ^ (prefixWord ++ tailWord_3661418).sum := by decide
  have hdescent : baseEnd_3661418 < baseStart_3661418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661431 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_3661431 : Nat := 118140960795 + 3661431 * 2 ^ 59
def prefixEnd_3661431 : Nat := 4983230072969 + 3 ^ 40 * 3661431 * 2
def baseEnd_3661431 : Nat := 1880073986272369368073891

theorem tailTrace_3661431 : CollatzResearch.WordTrace tailWord_3661431 prefixEnd_3661431 1880073986272369368073891 := by
  unfold tailWord_3661431
  simp only [CollatzResearch.WordTrace]
  refine ⟨133543359598268284475432147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89028906398845522983621431 133543359598268284475432147)
  ·
    refine ⟨200315039397402426713148221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133543359598268284475432147 200315039397402426713148221)
    ·
      refine ⟨75118139774025910017430583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200315039397402426713148221 75118139774025910017430583)
      ·
        refine ⟨112677209661038865026145875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75118139774025910017430583 112677209661038865026145875)
        ·
          refine ⟨169015814491558297539218813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112677209661038865026145875 169015814491558297539218813)
          ·
            refine ⟨63380930434334361577207055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169015814491558297539218813 63380930434334361577207055)
            ·
              refine ⟨95071395651501542365810583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63380930434334361577207055 95071395651501542365810583)
              ·
                refine ⟨142607093477252313548715875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95071395651501542365810583 142607093477252313548715875)
                ·
                  refine ⟨213910640215878470323073813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142607093477252313548715875 213910640215878470323073813)
                  ·
                    refine ⟨10027061260119303296394085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 213910640215878470323073813 10027061260119303296394085)
                    ·
                      refine ⟨1880073986272369368073891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10027061260119303296394085 1880073986272369368073891)
                      ·
                        rfl

theorem cell23_3661431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_3661431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661431 prefixEnd_3661431 := by exact prefixLift 3661431
  have htrace : WordTrace (prefixWord ++ tailWord_3661431) baseStart_3661431 baseEnd_3661431 := by
    simpa [prefixWord, tailWord_3661431, baseEnd_3661431] using wordTrace_append hprefix tailTrace_3661431
  have hstable : (prefixWord ++ tailWord_3661431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661431).length < 2 ^ (prefixWord ++ tailWord_3661431).sum := by decide
  have hdescent : baseEnd_3661431 < baseStart_3661431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661461 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3661461 : Nat := 118140960795 + 3661461 * 2 ^ 59
def prefixEnd_3661461 : Nat := 4983230072969 + 3 ^ 40 * 3661461 * 2
def baseEnd_3661461 : Nat := 1880089390692004250698753

theorem tailTrace_3661461 : CollatzResearch.WordTrace tailWord_3661461 prefixEnd_3661461 1880089390692004250698753 := by
  unfold tailWord_3661461
  simp only [CollatzResearch.WordTrace]
  refine ⟨133544453788159599599024237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89029635858773066399349491 133544453788159599599024237)
  ·
    refine ⟨50079170170559849849634089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133544453788159599599024237 50079170170559849849634089)
    ·
      refine ⟨37559377627919887387225567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50079170170559849849634089 37559377627919887387225567)
      ·
        refine ⟨56339066441879831080838351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37559377627919887387225567 56339066441879831080838351)
        ·
          refine ⟨84508599662819746621257527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56339066441879831080838351 84508599662819746621257527)
          ·
            refine ⟨126762899494229619931886291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84508599662819746621257527 126762899494229619931886291)
            ·
              refine ⟨190144349241344429897829437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126762899494229619931886291 190144349241344429897829437)
              ·
                refine ⟨71304130965504161211686039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190144349241344429897829437 71304130965504161211686039)
                ·
                  refine ⟨106956196448256241817529059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71304130965504161211686039 106956196448256241817529059)
                  ·
                    refine ⟨160434294672384362726293589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106956196448256241817529059 160434294672384362726293589)
                    ·
                      refine ⟨1880089390692004250698753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 160434294672384362726293589 1880089390692004250698753)
                      ·
                        rfl

theorem cell23_3661461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3661461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661461 prefixEnd_3661461 := by exact prefixLift 3661461
  have htrace : WordTrace (prefixWord ++ tailWord_3661461) baseStart_3661461 baseEnd_3661461 := by
    simpa [prefixWord, tailWord_3661461, baseEnd_3661461] using wordTrace_append hprefix tailTrace_3661461
  have hstable : (prefixWord ++ tailWord_3661461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661461).length < 2 ^ (prefixWord ++ tailWord_3661461).sum := by decide
  have hdescent : baseEnd_3661461 < baseStart_3661461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661481 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_3661481 : Nat := 118140960795 + 3661481 * 2 ^ 59
def prefixEnd_3661481 : Nat := 4983230072969 + 3 ^ 40 * 3661481 * 2
def baseEnd_3661481 : Nat := 1880099660305094172448661

theorem tailTrace_3661481 : CollatzResearch.WordTrace tailWord_3661481 prefixEnd_3661481 1880099660305094172448661 := by
  unfold tailWord_3661481
  simp only [CollatzResearch.WordTrace]
  refine ⟨133545183248087143014752297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89030122165391428676501531 133545183248087143014752297)
  ·
    refine ⟨100158887436065357261064223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133545183248087143014752297 100158887436065357261064223)
    ·
      refine ⟨150238331154098035891596335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100158887436065357261064223 150238331154098035891596335)
      ·
        refine ⟨225357496731147053837394503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150238331154098035891596335 225357496731147053837394503)
        ·
          refine ⟨338036245096720580756091755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225357496731147053837394503 338036245096720580756091755)
          ·
            refine ⟨507054367645080871134137633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338036245096720580756091755 507054367645080871134137633)
            ·
              refine ⟨380290775733810653350603225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507054367645080871134137633 380290775733810653350603225)
              ·
                refine ⟨285218081800357990012952419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380290775733810653350603225 285218081800357990012952419)
                ·
                  refine ⟨427827122700536985019428629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285218081800357990012952419 427827122700536985019428629)
                  ·
                    refine ⟨20054396376587671172785717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 427827122700536985019428629 20054396376587671172785717)
                    ·
                      refine ⟨1880099660305094172448661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20054396376587671172785717 1880099660305094172448661)
                      ·
                        rfl

theorem cell23_3661481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_3661481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661481 prefixEnd_3661481 := by exact prefixLift 3661481
  have htrace : WordTrace (prefixWord ++ tailWord_3661481) baseStart_3661481 baseEnd_3661481 := by
    simpa [prefixWord, tailWord_3661481, baseEnd_3661481] using wordTrace_append hprefix tailTrace_3661481
  have hstable : (prefixWord ++ tailWord_3661481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661481).length < 2 ^ (prefixWord ++ tailWord_3661481).sum := by decide
  have hdescent : baseEnd_3661481 < baseStart_3661481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661518 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_3661518 : Nat := 118140960795 + 3661518 * 2 ^ 59
def prefixEnd_3661518 : Nat := 4983230072969 + 3 ^ 40 * 3661518 * 2
def baseEnd_3661518 : Nat := 626706219696436842561997

theorem tailTrace_3661518 : CollatzResearch.WordTrace tailWord_3661518 prefixEnd_3661518 626706219696436842561997 := by
  unfold tailWord_3661518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16693316593619137291731151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89031021832635398889232805 16693316593619137291731151)
  ·
    refine ⟨25039974890428705937596727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16693316593619137291731151 25039974890428705937596727)
    ·
      refine ⟨37559962335643058906395091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25039974890428705937596727 37559962335643058906395091)
      ·
        refine ⟨56339943503464588359592637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37559962335643058906395091 56339943503464588359592637)
        ·
          refine ⟨21127478813799220634847239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56339943503464588359592637 21127478813799220634847239)
          ·
            refine ⟨31691218220698830952270859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21127478813799220634847239 31691218220698830952270859)
            ·
              refine ⟨47536827331048246428406289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31691218220698830952270859 47536827331048246428406289)
              ·
                refine ⟨35652620498286184821304717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47536827331048246428406289 35652620498286184821304717)
                ·
                  refine ⟨13369732686857319307989269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35652620498286184821304717 13369732686857319307989269)
                  ·
                    refine ⟨626706219696436842561997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13369732686857319307989269 626706219696436842561997)
                    ·
                      rfl

theorem cell23_3661518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_3661518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661518 prefixEnd_3661518 := by exact prefixLift 3661518
  have htrace : WordTrace (prefixWord ++ tailWord_3661518) baseStart_3661518 baseEnd_3661518 := by
    simpa [prefixWord, tailWord_3661518, baseEnd_3661518] using wordTrace_append hprefix tailTrace_3661518
  have hstable : (prefixWord ++ tailWord_3661518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661518).length < 2 ^ (prefixWord ++ tailWord_3661518).sum := by decide
  have hdescent : baseEnd_3661518 < baseStart_3661518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661528 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_3661528 : Nat := 118140960795 + 3661528 * 2 ^ 59
def prefixEnd_3661528 : Nat := 4983230072969 + 3 ^ 40 * 3661528 * 2
def baseEnd_3661528 : Nat := 1880123793895855488560945

theorem tailTrace_3661528 : CollatzResearch.WordTrace tailWord_3661528 prefixEnd_3661528 1880123793895855488560945 := by
  unfold tailWord_3661528
  simp only [CollatzResearch.WordTrace]
  refine ⟨66773448739458435020856619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89031264985944580027808825 66773448739458435020856619)
  ·
    refine ⟨100160173109187652531284929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66773448739458435020856619 100160173109187652531284929)
    ·
      refine ⟨75120129831890739398463697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100160173109187652531284929 75120129831890739398463697)
      ·
        refine ⟨56340097373918054548847773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75120129831890739398463697 56340097373918054548847773)
        ·
          refine ⟨21127536515219270455817915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56340097373918054548847773 21127536515219270455817915)
          ·
            refine ⟨31691304772828905683726873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21127536515219270455817915 31691304772828905683726873)
            ·
              refine ⟨23768478579621679262795155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31691304772828905683726873 23768478579621679262795155)
              ·
                refine ⟨35652717869432518894192733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23768478579621679262795155 35652717869432518894192733)
                ·
                  refine ⟨13369769201037194585322275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35652717869432518894192733 13369769201037194585322275)
                  ·
                    refine ⟨20054653801555791877983413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13369769201037194585322275 20054653801555791877983413)
                    ·
                      refine ⟨1880123793895855488560945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20054653801555791877983413 1880123793895855488560945)
                      ·
                        rfl

theorem cell23_3661528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_3661528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661528 prefixEnd_3661528 := by exact prefixLift 3661528
  have htrace : WordTrace (prefixWord ++ tailWord_3661528) baseStart_3661528 baseEnd_3661528 := by
    simpa [prefixWord, tailWord_3661528, baseEnd_3661528] using wordTrace_append hprefix tailTrace_3661528
  have hstable : (prefixWord ++ tailWord_3661528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661528).length < 2 ^ (prefixWord ++ tailWord_3661528).sum := by decide
  have hdescent : baseEnd_3661528 < baseStart_3661528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661535 : List Nat := [1, 1, 2, 3, 2, 2, 1, 5, 2, 4]
def baseStart_3661535 : Nat := 118140960795 + 3661535 * 2 ^ 59
def prefixEnd_3661535 : Nat := 4983230072969 + 3 ^ 40 * 3661535 * 2
def baseEnd_3661535 : Nat := 626709129420145653724471

theorem tailTrace_3661535 : CollatzResearch.WordTrace tailWord_3661535 prefixEnd_3661535 626709129420145653724471 := by
  unfold tailWord_3661535
  simp only [CollatzResearch.WordTrace]
  refine ⟨133547152789891510237218059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89031435193261006824812039 133547152789891510237218059)
  ·
    refine ⟨200320729184837265355827089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133547152789891510237218059 200320729184837265355827089)
    ·
      refine ⟨150240546888627949016870317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200320729184837265355827089 150240546888627949016870317)
      ·
        refine ⟨56340205083235480881326369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150240546888627949016870317 56340205083235480881326369)
        ·
          refine ⟨42255153812426610660994777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56340205083235480881326369 42255153812426610660994777)
          ·
            refine ⟨31691365359319957995746083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42255153812426610660994777 31691365359319957995746083)
            ·
              refine ⟨47537048038979936993619125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31691365359319957995746083 47537048038979936993619125)
              ·
                refine ⟨4456598253654369093151793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47537048038979936993619125 4456598253654369093151793)
                ·
                  refine ⟨3342448690240776819863845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4456598253654369093151793 3342448690240776819863845)
                  ·
                    refine ⟨626709129420145653724471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3342448690240776819863845 626709129420145653724471)
                    ·
                      rfl

theorem cell23_3661535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 4].length) (baseStart_3661535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661535 prefixEnd_3661535 := by exact prefixLift 3661535
  have htrace : WordTrace (prefixWord ++ tailWord_3661535) baseStart_3661535 baseEnd_3661535 := by
    simpa [prefixWord, tailWord_3661535, baseEnd_3661535] using wordTrace_append hprefix tailTrace_3661535
  have hstable : (prefixWord ++ tailWord_3661535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661535).length < 2 ^ (prefixWord ++ tailWord_3661535).sum := by decide
  have hdescent : baseEnd_3661535 < baseStart_3661535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661545 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 3]
def baseStart_3661545 : Nat := 118140960795 + 3661545 * 2 ^ 59
def prefixEnd_3661545 : Nat := 4983230072969 + 3 ^ 40 * 3661545 * 2
def baseEnd_3661545 : Nat := 1880132523066981922048367

theorem tailTrace_3661545 : CollatzResearch.WordTrace tailWord_3661545 prefixEnd_3661545 1880132523066981922048367 := by
  unfold tailWord_3661545
  simp only [CollatzResearch.WordTrace]
  refine ⟨133547517519855281945082089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89031678346570187963388059 133547517519855281945082089)
  ·
    refine ⟨100160638139891461458811567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133547517519855281945082089 100160638139891461458811567)
    ·
      refine ⟨150240957209837192188217351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100160638139891461458811567 150240957209837192188217351)
      ·
        refine ⟨225361435814755788282326027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150240957209837192188217351 225361435814755788282326027)
        ·
          refine ⟨338042153722133682423489041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225361435814755788282326027 338042153722133682423489041)
          ·
            refine ⟨253531615291600261817616781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338042153722133682423489041 253531615291600261817616781)
            ·
              refine ⟨95074355734350098181606293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253531615291600261817616781 95074355734350098181606293)
              ·
                refine ⟨4456610425047660852262795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95074355734350098181606293 4456610425047660852262795)
                ·
                  refine ⟨6684915637571491278394193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456610425047660852262795 6684915637571491278394193)
                  ·
                    refine ⟨5013686728178618458795645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6684915637571491278394193 5013686728178618458795645)
                    ·
                      refine ⟨1880132523066981922048367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5013686728178618458795645 1880132523066981922048367)
                      ·
                        rfl

theorem cell23_3661545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 3].length) (baseStart_3661545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661545 prefixEnd_3661545 := by exact prefixLift 3661545
  have htrace : WordTrace (prefixWord ++ tailWord_3661545) baseStart_3661545 baseEnd_3661545 := by
    simpa [prefixWord, tailWord_3661545, baseEnd_3661545] using wordTrace_append hprefix tailTrace_3661545
  have hstable : (prefixWord ++ tailWord_3661545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661545).length < 2 ^ (prefixWord ++ tailWord_3661545).sum := by decide
  have hdescent : baseEnd_3661545 < baseStart_3661545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661556 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3661556 : Nat := 118140960795 + 3661556 * 2 ^ 59
def prefixEnd_3661556 : Nat := 4983230072969 + 3 ^ 40 * 3661556 * 2
def baseEnd_3661556 : Nat := 626712723784727126336939

theorem tailTrace_3661556 : CollatzResearch.WordTrace tailWord_3661556 prefixEnd_3661556 626712723784727126336939 := by
  unfold tailWord_3661556
  simp only [CollatzResearch.WordTrace]
  refine ⟨66773959361407715411866261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89031945815210287215821681 66773959361407715411866261)
  ·
    refine ⟨3130029345065986659931231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66773959361407715411866261 3130029345065986659931231)
    ·
      refine ⟨4695044017598979989896847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3130029345065986659931231 4695044017598979989896847)
      ·
        refine ⟨7042566026398469984845271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4695044017598979989896847 7042566026398469984845271)
        ·
          refine ⟨10563849039597704977267907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042566026398469984845271 10563849039597704977267907)
          ·
            refine ⟨15845773559396557465901861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10563849039597704977267907 15845773559396557465901861)
            ·
              refine ⟨2971082542386854524856599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15845773559396557465901861 2971082542386854524856599)
              ·
                refine ⟨4456623813580281787284899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971082542386854524856599 4456623813580281787284899)
                ·
                  refine ⟨6684935720370422680927349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456623813580281787284899 6684935720370422680927349)
                  ·
                    refine ⟨626712723784727126336939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6684935720370422680927349 626712723784727126336939)
                    ·
                      rfl

theorem cell23_3661556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3661556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661556 prefixEnd_3661556 := by exact prefixLift 3661556
  have htrace : WordTrace (prefixWord ++ tailWord_3661556) baseStart_3661556 baseEnd_3661556 := by
    simpa [prefixWord, tailWord_3661556, baseEnd_3661556] using wordTrace_append hprefix tailTrace_3661556
  have hstable : (prefixWord ++ tailWord_3661556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661556).length < 2 ^ (prefixWord ++ tailWord_3661556).sum := by decide
  have hdescent : baseEnd_3661556 < baseStart_3661556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661559 : List Nat := [1, 1, 3, 1, 1, 1, 5, 5, 1, 2, 2]
def baseStart_3661559 : Nat := 118140960795 + 3661559 * 2 ^ 59
def prefixEnd_3661559 : Nat := 4983230072969 + 3 ^ 40 * 3661559 * 2
def baseEnd_3661559 : Nat := 1880139711796144867273303

theorem tailTrace_3661559 : CollatzResearch.WordTrace tailWord_3661559 prefixEnd_3661559 1880139711796144867273303 := by
  unfold tailWord_3661559
  simp only [CollatzResearch.WordTrace]
  refine ⟨133548028141804562336091731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89032018761203041557394487 133548028141804562336091731)
  ·
    refine ⟨200322042212706843504137597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133548028141804562336091731 200322042212706843504137597)
    ·
      refine ⟨75120765829765066314051599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200322042212706843504137597 75120765829765066314051599)
      ·
        refine ⟨112681148744647599471077399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75120765829765066314051599 112681148744647599471077399)
        ·
          refine ⟨169021723116971399206616099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112681148744647599471077399 169021723116971399206616099)
          ·
            refine ⟨253532584675457098809924149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169021723116971399206616099 253532584675457098809924149)
            ·
              refine ⟨23768679813324103013430389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253532584675457098809924149 23768679813324103013430389)
              ·
                refine ⟨2228313732499134657509099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23768679813324103013430389 2228313732499134657509099)
                ·
                  refine ⟨3342470598748701986263649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228313732499134657509099 3342470598748701986263649)
                  ·
                    refine ⟨2506852949061526489697737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3342470598748701986263649 2506852949061526489697737)
                    ·
                      refine ⟨1880139711796144867273303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2506852949061526489697737 1880139711796144867273303)
                      ·
                        rfl

theorem cell23_3661559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 2, 2].length) (baseStart_3661559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661559 prefixEnd_3661559 := by exact prefixLift 3661559
  have htrace : WordTrace (prefixWord ++ tailWord_3661559) baseStart_3661559 baseEnd_3661559 := by
    simpa [prefixWord, tailWord_3661559, baseEnd_3661559] using wordTrace_append hprefix tailTrace_3661559
  have hstable : (prefixWord ++ tailWord_3661559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661559).length < 2 ^ (prefixWord ++ tailWord_3661559).sum := by decide
  have hdescent : baseEnd_3661559 < baseStart_3661559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661586 : List Nat := [3, 2, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3661586 : Nat := 118140960795 + 3661586 * 2 ^ 59
def prefixEnd_3661586 : Nat := 4983230072969 + 3 ^ 40 * 3661586 * 2
def baseEnd_3661586 : Nat := 626717858591272087211893

theorem tailTrace_3661586 : CollatzResearch.WordTrace tailWord_3661586 prefixEnd_3661586 626717858591272087211893 := by
  unfold tailWord_3661586
  simp only [CollatzResearch.WordTrace]
  refine ⟨33387253228176686486831153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89032675275137830631549741 33387253228176686486831153)
  ·
    refine ⟨25040439921132514865123365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33387253228176686486831153 25040439921132514865123365)
    ·
      refine ⟨4695082485212346537210631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25040439921132514865123365 4695082485212346537210631)
      ·
        refine ⟨7042623727818519805815947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4695082485212346537210631 7042623727818519805815947)
        ·
          refine ⟨10563935591727779708723921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042623727818519805815947 10563935591727779708723921)
          ·
            refine ⟨7922951693795834781542941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10563935591727779708723921 7922951693795834781542941)
            ·
              refine ⟨2971106885173438043078603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7922951693795834781542941 2971106885173438043078603)
              ·
                refine ⟨4456660327760157064617905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971106885173438043078603 4456660327760157064617905)
                ·
                  refine ⟨3342495245820117798463429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4456660327760157064617905 3342495245820117798463429)
                  ·
                    refine ⟨626717858591272087211893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3342495245820117798463429 626717858591272087211893)
                    ·
                      rfl

theorem cell23_3661586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3661586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661586 prefixEnd_3661586 := by exact prefixLift 3661586
  have htrace : WordTrace (prefixWord ++ tailWord_3661586) baseStart_3661586 baseEnd_3661586 := by
    simpa [prefixWord, tailWord_3661586, baseEnd_3661586] using wordTrace_append hprefix tailTrace_3661586
  have hstable : (prefixWord ++ tailWord_3661586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661586).length < 2 ^ (prefixWord ++ tailWord_3661586).sum := by decide
  have hdescent : baseEnd_3661586 < baseStart_3661586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661592 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 2, 1, 3]
def baseStart_3661592 : Nat := 118140960795 + 3661592 * 2 ^ 59
def prefixEnd_3661592 : Nat := 4983230072969 + 3 ^ 40 * 3661592 * 2
def baseEnd_3661592 : Nat := 1880156656657743238160651

theorem tailTrace_3661592 : CollatzResearch.WordTrace tailWord_3661592 prefixEnd_3661592 1880156656657743238160651 := by
  unfold tailWord_3661592
  simp only [CollatzResearch.WordTrace]
  refine ⟨66774615875342504486021515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89032821167123339314695353 66774615875342504486021515)
  ·
    refine ⟨100161923813013756729032273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66774615875342504486021515 100161923813013756729032273)
    ·
      refine ⟨75121442859760317546774205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100161923813013756729032273 75121442859760317546774205)
      ·
        refine ⟨28170541072410119080040327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75121442859760317546774205 28170541072410119080040327)
        ·
          refine ⟨42255811608615178620060491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28170541072410119080040327 42255811608615178620060491)
          ·
            refine ⟨63383717412922767930090737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42255811608615178620060491 63383717412922767930090737)
            ·
              refine ⟨47537788059692075947568053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63383717412922767930090737 47537788059692075947568053)
              ·
                refine ⟨4456667630596132120084505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47537788059692075947568053 4456667630596132120084505)
                ·
                  refine ⟨3342500722947099090063379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4456667630596132120084505 3342500722947099090063379)
                  ·
                    refine ⟨5013751084420648635095069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3342500722947099090063379 5013751084420648635095069)
                    ·
                      refine ⟨1880156656657743238160651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5013751084420648635095069 1880156656657743238160651)
                      ·
                        rfl

theorem cell23_3661592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_3661592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661592 prefixEnd_3661592 := by exact prefixLift 3661592
  have htrace : WordTrace (prefixWord ++ tailWord_3661592) baseStart_3661592 baseEnd_3661592 := by
    simpa [prefixWord, tailWord_3661592, baseEnd_3661592] using wordTrace_append hprefix tailTrace_3661592
  have hstable : (prefixWord ++ tailWord_3661592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661592).length < 2 ^ (prefixWord ++ tailWord_3661592).sum := by decide
  have hdescent : baseEnd_3661592 < baseStart_3661592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661672 : List Nat := [2, 1, 4, 2, 1, 1, 2, 5, 5]
def baseStart_3661672 : Nat := 118140960795 + 3661672 * 2 ^ 59
def prefixEnd_3661672 : Nat := 4983230072969 + 3 ^ 40 * 3661672 * 2
def baseEnd_3661672 : Nat := 208910859456678102795587

theorem tailTrace_3661672 : CollatzResearch.WordTrace tailWord_3661672 prefixEnd_3661672 208910859456678102795587 := by
  unfold tailWord_3661672
  simp only [CollatzResearch.WordTrace]
  refine ⟨66776074795197591317477635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89034766393596788423303513 66776074795197591317477635)
  ·
    refine ⟨100164112192796386976216453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66776074795197591317477635 100164112192796386976216453)
    ·
      refine ⟨18780771036149322558040585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100164112192796386976216453 18780771036149322558040585)
      ·
        refine ⟨14085578277111991918530439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18780771036149322558040585 14085578277111991918530439)
        ·
          refine ⟨21128367415667987877795659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14085578277111991918530439 21128367415667987877795659)
          ·
            refine ⟨31692551123501981816693489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21128367415667987877795659 31692551123501981816693489)
            ·
              refine ⟨23769413342626486362520117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31692551123501981816693489 23769413342626486362520117)
              ·
                refine ⟨2228382500871233096486261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23769413342626486362520117 2228382500871233096486261)
                ·
                  refine ⟨208910859456678102795587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2228382500871233096486261 208910859456678102795587)
                  ·
                    rfl

theorem cell23_3661672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 5].length) (baseStart_3661672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661672 prefixEnd_3661672 := by exact prefixLift 3661672
  have htrace : WordTrace (prefixWord ++ tailWord_3661672) baseStart_3661672 baseEnd_3661672 := by
    simpa [prefixWord, tailWord_3661672, baseEnd_3661672] using wordTrace_append hprefix tailTrace_3661672
  have hstable : (prefixWord ++ tailWord_3661672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661672).length < 2 ^ (prefixWord ++ tailWord_3661672).sum := by decide
  have hdescent : baseEnd_3661672 < baseStart_3661672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661705 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_3661705 : Nat := 118140960795 + 3661705 * 2 ^ 59
def prefixEnd_3661705 : Nat := 4983230072969 + 3 ^ 40 * 3661705 * 2
def baseEnd_3661705 : Nat := 1880214679971701296047631

theorem tailTrace_3661705 : CollatzResearch.WordTrace tailWord_3661705 prefixEnd_3661705 1880214679971701296047631 := by
  unfold tailWord_3661705
  simp only [CollatzResearch.WordTrace]
  refine ⟨133553353199275629270906569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89035568799517086180604379 133553353199275629270906569)
  ·
    refine ⟨100165014899456721953179927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133553353199275629270906569 100165014899456721953179927)
    ·
      refine ⟨150247522349185082929769891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100165014899456721953179927 150247522349185082929769891)
      ·
        refine ⟨225371283523777624394654837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150247522349185082929769891 225371283523777624394654837)
        ·
          refine ⟨21128557830354152286998891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225371283523777624394654837 21128557830354152286998891)
          ·
            refine ⟨31692836745531228430498337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21128557830354152286998891 31692836745531228430498337)
            ·
              refine ⟨23769627559148421322873753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31692836745531228430498337 23769627559148421322873753)
              ·
                refine ⟨17827220669361315992155315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23769627559148421322873753 17827220669361315992155315)
                ·
                  refine ⟨26740831004041973988232973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17827220669361315992155315 26740831004041973988232973)
                  ·
                    refine ⟨10027811626515740245587365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26740831004041973988232973 10027811626515740245587365)
                    ·
                      refine ⟨1880214679971701296047631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10027811626515740245587365 1880214679971701296047631)
                      ·
                        rfl

theorem cell23_3661705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_3661705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661705 prefixEnd_3661705 := by exact prefixLift 3661705
  have htrace : WordTrace (prefixWord ++ tailWord_3661705) baseStart_3661705 baseEnd_3661705 := by
    simpa [prefixWord, tailWord_3661705, baseEnd_3661705] using wordTrace_append hprefix tailTrace_3661705
  have hstable : (prefixWord ++ tailWord_3661705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661705).length < 2 ^ (prefixWord ++ tailWord_3661705).sum := by decide
  have hdescent : baseEnd_3661705 < baseStart_3661705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661722 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3661722 : Nat := 118140960795 + 3661722 * 2 ^ 59
def prefixEnd_3661722 : Nat := 4983230072969 + 3 ^ 40 * 3661722 * 2
def baseEnd_3661722 : Nat := 1880223409142827729535053

theorem tailTrace_3661722 : CollatzResearch.WordTrace tailWord_3661722 prefixEnd_3661722 1880223409142827729535053 := by
  unfold tailWord_3661722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33388493310053510293568855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89035982160142694116183613 33388493310053510293568855)
  ·
    refine ⟨50082739965080265440353283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33388493310053510293568855 50082739965080265440353283)
    ·
      refine ⟨75124109947620398160529925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50082739965080265440353283 75124109947620398160529925)
      ·
        refine ⟨14085770615178824655099361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75124109947620398160529925 14085770615178824655099361)
        ·
          refine ⟨10564327961384118491324521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14085770615178824655099361 10564327961384118491324521)
          ·
            refine ⟨7923245971038088868493391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10564327961384118491324521 7923245971038088868493391)
            ·
              refine ⟨11884868956557133302740087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923245971038088868493391 11884868956557133302740087)
              ·
                refine ⟨17827303434835699954110131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11884868956557133302740087 17827303434835699954110131)
                ·
                  refine ⟨26740955152253549931165197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17827303434835699954110131 26740955152253549931165197)
                  ·
                    refine ⟨10027858182095081224186949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26740955152253549931165197 10027858182095081224186949)
                    ·
                      refine ⟨1880223409142827729535053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10027858182095081224186949 1880223409142827729535053)
                      ·
                        rfl

theorem cell23_3661722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3661722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661722 prefixEnd_3661722 := by exact prefixLift 3661722
  have htrace : WordTrace (prefixWord ++ tailWord_3661722) baseStart_3661722 baseEnd_3661722 := by
    simpa [prefixWord, tailWord_3661722, baseEnd_3661722] using wordTrace_append hprefix tailTrace_3661722
  have hstable : (prefixWord ++ tailWord_3661722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661722).length < 2 ^ (prefixWord ++ tailWord_3661722).sum := by decide
  have hdescent : baseEnd_3661722 < baseStart_3661722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661749 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3661749 : Nat := 118140960795 + 3661749 * 2 ^ 59
def prefixEnd_3661749 : Nat := 4983230072969 + 3 ^ 40 * 3661749 * 2
def baseEnd_3661749 : Nat := 626745757706833041299143

theorem tailTrace_3661749 : CollatzResearch.WordTrace tailWord_3661749 prefixEnd_3661749 626745757706833041299143 := by
  unfold tailWord_3661749
  simp only [CollatzResearch.WordTrace]
  refine ⟨133554958011116224785508301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89036638674077483190338867 133554958011116224785508301)
  ·
    refine ⟨50083109254168584294565613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133554958011116224785508301 50083109254168584294565613)
    ·
      refine ⟨18781165970313219110462105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50083109254168584294565613 18781165970313219110462105)
      ·
        refine ⟨14085874477734914332846579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18781165970313219110462105 14085874477734914332846579)
        ·
          refine ⟨21128811716602371499269869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14085874477734914332846579 21128811716602371499269869)
          ·
            refine ⟨7923304393725889312226201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21128811716602371499269869 7923304393725889312226201)
            ·
              refine ⟨5942478295294416984169651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7923304393725889312226201 5942478295294416984169651)
              ·
                refine ⟨8913717442941625476254477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942478295294416984169651 8913717442941625476254477)
                ·
                  refine ⟨3342644041103109553595429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8913717442941625476254477 3342644041103109553595429)
                  ·
                    refine ⟨626745757706833041299143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3342644041103109553595429 626745757706833041299143)
                    ·
                      rfl

theorem cell23_3661749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3661749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661749 prefixEnd_3661749 := by exact prefixLift 3661749
  have htrace : WordTrace (prefixWord ++ tailWord_3661749) baseStart_3661749 baseEnd_3661749 := by
    simpa [prefixWord, tailWord_3661749, baseEnd_3661749] using wordTrace_append hprefix tailTrace_3661749
  have hstable : (prefixWord ++ tailWord_3661749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661749).length < 2 ^ (prefixWord ++ tailWord_3661749).sum := by decide
  have hdescent : baseEnd_3661749 < baseStart_3661749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661755 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 3]
def baseStart_3661755 : Nat := 118140960795 + 3661755 * 2 ^ 59
def prefixEnd_3661755 : Nat := 4983230072969 + 3 ^ 40 * 3661755 * 2
def baseEnd_3661755 : Nat := 1880240354004426100422401

theorem tailTrace_3661755 : CollatzResearch.WordTrace tailWord_3661755 prefixEnd_3661755 1880240354004426100422401 := by
  unfold tailWord_3661755
  simp only [CollatzResearch.WordTrace]
  refine ⟨133555176849094487810226719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89036784566062991873484479 133555176849094487810226719)
  ·
    refine ⟨200332765273641731715340079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133555176849094487810226719 200332765273641731715340079)
    ·
      refine ⟨300499147910462597573010119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200332765273641731715340079 300499147910462597573010119)
      ·
        refine ⟨450748721865693896359515179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300499147910462597573010119 450748721865693896359515179)
        ·
          refine ⟨676123082798540844539272769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450748721865693896359515179 676123082798540844539272769)
          ·
            refine ⟨507092312098905633404454577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676123082798540844539272769 507092312098905633404454577)
            ·
              refine ⟨380319234074179225053340933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507092312098905633404454577 380319234074179225053340933)
              ·
                refine ⟨71309856388908604697501425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380319234074179225053340933 71309856388908604697501425)
                ·
                  refine ⟨53482392291681453523126069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71309856388908604697501425 53482392291681453523126069)
                  ·
                    refine ⟨5013974277345136267793069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53482392291681453523126069 5013974277345136267793069)
                    ·
                      refine ⟨1880240354004426100422401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5013974277345136267793069 1880240354004426100422401)
                      ·
                        rfl

theorem cell23_3661755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 3].length) (baseStart_3661755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661755 prefixEnd_3661755 := by exact prefixLift 3661755
  have htrace : WordTrace (prefixWord ++ tailWord_3661755) baseStart_3661755 baseEnd_3661755 := by
    simpa [prefixWord, tailWord_3661755, baseEnd_3661755] using wordTrace_append hprefix tailTrace_3661755
  have hstable : (prefixWord ++ tailWord_3661755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661755).length < 2 ^ (prefixWord ++ tailWord_3661755).sum := by decide
  have hdescent : baseEnd_3661755 < baseStart_3661755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661806 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_3661806 : Nat := 118140960795 + 3661806 * 2 ^ 59
def prefixEnd_3661806 : Nat := 4983230072969 + 3 ^ 40 * 3661806 * 2
def baseEnd_3661806 : Nat := 1880266541517805400884667

theorem tailTrace_3661806 : CollatzResearch.WordTrace tailWord_3661806 prefixEnd_3661806 1880266541517805400884667 := by
  unfold tailWord_3661806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16694629621488715440041659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89038024647939815680222181 16694629621488715440041659)
  ·
    refine ⟨25041944432233073160062489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16694629621488715440041659 25041944432233073160062489)
    ·
      refine ⟨18781458324174804870046867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25041944432233073160062489 18781458324174804870046867)
      ·
        refine ⟨28172187486262207305070301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18781458324174804870046867 28172187486262207305070301)
        ·
          refine ⟨10564570307348327739401363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28172187486262207305070301 10564570307348327739401363)
          ·
            refine ⟨15846855461022491609102045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10564570307348327739401363 15846855461022491609102045)
            ·
              refine ⟨5942570797883434353413267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15846855461022491609102045 5942570797883434353413267)
              ·
                refine ⟨8913856196825151530119901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942570797883434353413267 8913856196825151530119901)
                ·
                  refine ⟨3342696073809431823794963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8913856196825151530119901 3342696073809431823794963)
                  ·
                    refine ⟨5014044110714147735692445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3342696073809431823794963 5014044110714147735692445)
                    ·
                      refine ⟨1880266541517805400884667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5014044110714147735692445 1880266541517805400884667)
                      ·
                        rfl

theorem cell23_3661806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_3661806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661806 prefixEnd_3661806 := by exact prefixLift 3661806
  have htrace : WordTrace (prefixWord ++ tailWord_3661806) baseStart_3661806 baseEnd_3661806 := by
    simpa [prefixWord, tailWord_3661806, baseEnd_3661806] using wordTrace_append hprefix tailTrace_3661806
  have hstable : (prefixWord ++ tailWord_3661806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661806).length < 2 ^ (prefixWord ++ tailWord_3661806).sum := by decide
  have hdescent : baseEnd_3661806 < baseStart_3661806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661829 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 4]
def baseStart_3661829 : Nat := 118140960795 + 3661829 * 2 ^ 59
def prefixEnd_3661829 : Nat := 4983230072969 + 3 ^ 40 * 3661829 * 2
def baseEnd_3661829 : Nat := 1880278351572858810897061

theorem tailTrace_3661829 : CollatzResearch.WordTrace tailWord_3661829 prefixEnd_3661829 1880278351572858810897061 := by
  unfold tailWord_3661829
  simp only [CollatzResearch.WordTrace]
  refine ⟨133557875850826398448420541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89038583900550932298947027 133557875850826398448420541)
  ·
    refine ⟨50084203444059899418157703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133557875850826398448420541 50084203444059899418157703)
    ·
      refine ⟨75126305166089849127236555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50084203444059899418157703 75126305166089849127236555)
      ·
        refine ⟨112689457749134773690854833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75126305166089849127236555 112689457749134773690854833)
        ·
          refine ⟨84517093311851080268141125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112689457749134773690854833 84517093311851080268141125)
          ·
            refine ⟨15846954995972077550276461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84517093311851080268141125 15846954995972077550276461)
            ·
              refine ⟨5942608123489529081353673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15846954995972077550276461 5942608123489529081353673)
              ·
                refine ⟨4456956092617146811015255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5942608123489529081353673 4456956092617146811015255)
                ·
                  refine ⟨6685434138925720216522883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456956092617146811015255 6685434138925720216522883)
                  ·
                    refine ⟨10028151208388580324784325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6685434138925720216522883 10028151208388580324784325)
                    ·
                      refine ⟨1880278351572858810897061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10028151208388580324784325 1880278351572858810897061)
                      ·
                        rfl

theorem cell23_3661829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_3661829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661829 prefixEnd_3661829 := by exact prefixLift 3661829
  have htrace : WordTrace (prefixWord ++ tailWord_3661829) baseStart_3661829 baseEnd_3661829 := by
    simpa [prefixWord, tailWord_3661829, baseEnd_3661829] using wordTrace_append hprefix tailTrace_3661829
  have hstable : (prefixWord ++ tailWord_3661829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661829).length < 2 ^ (prefixWord ++ tailWord_3661829).sum := by decide
  have hdescent : baseEnd_3661829 < baseStart_3661829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661835 : List Nat := [1, 1, 1, 1, 6, 1, 1, 11]
def baseStart_3661835 : Nat := 118140960795 + 3661835 * 2 ^ 59
def prefixEnd_3661835 : Nat := 4983230072969 + 3 ^ 40 * 3661835 * 2
def baseEnd_3661835 : Nat := 69640053053955029163779

theorem tailTrace_3661835 : CollatzResearch.WordTrace tailWord_3661835 prefixEnd_3661835 69640053053955029163779 := by
  unfold tailWord_3661835
  simp only [CollatzResearch.WordTrace]
  refine ⟨133558094688804661473138959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89038729792536440982092639 133558094688804661473138959)
  ·
    refine ⟨200337142033206992209708439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133558094688804661473138959 200337142033206992209708439)
    ·
      refine ⟨300505713049810488314562659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200337142033206992209708439 300505713049810488314562659)
      ·
        refine ⟨450758569574715732471843989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300505713049810488314562659 450758569574715732471843989)
        ·
          refine ⟨21129307948814799959617687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 450758569574715732471843989 21129307948814799959617687)
          ·
            refine ⟨31693961923222199939426531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21129307948814799959617687 31693961923222199939426531)
            ·
              refine ⟨47540942884833299909139797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31693961923222199939426531 47540942884833299909139797)
              ·
                refine ⟨69640053053955029163779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 47540942884833299909139797 69640053053955029163779)
                ·
                  rfl

theorem cell23_3661835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 11].length) (baseStart_3661835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661835 prefixEnd_3661835 := by exact prefixLift 3661835
  have htrace : WordTrace (prefixWord ++ tailWord_3661835) baseStart_3661835 baseEnd_3661835 := by
    simpa [prefixWord, tailWord_3661835, baseEnd_3661835] using wordTrace_append hprefix tailTrace_3661835
  have hstable : (prefixWord ++ tailWord_3661835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661835).length < 2 ^ (prefixWord ++ tailWord_3661835).sum := by decide
  have hdescent : baseEnd_3661835 < baseStart_3661835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661857 : List Nat := [1, 2, 3, 2, 5, 1, 2, 2, 1, 1, 3]
def baseStart_3661857 : Nat := 118140960795 + 3661857 * 2 ^ 59
def prefixEnd_3661857 : Nat := 4983230072969 + 3 ^ 40 * 3661857 * 2
def baseEnd_3661857 : Nat := 1880292729031184701346933

theorem tailTrace_3661857 : CollatzResearch.WordTrace tailWord_3661857 prefixEnd_3661857 1880292729031184701346933 := by
  unfold tailWord_3661857
  simp only [CollatzResearch.WordTrace]
  refine ⟨133558897094724959230439825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89039264729816639486959883 133558897094724959230439825)
  ·
    refine ⟨100169172821043719422829869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133558897094724959230439825 100169172821043719422829869)
    ·
      refine ⟨37563439807891394783561201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100169172821043719422829869 37563439807891394783561201)
      ·
        refine ⟨28172579855918546087670901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37563439807891394783561201 28172579855918546087670901)
        ·
          refine ⟨2641179361492363695719147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28172579855918546087670901 2641179361492363695719147)
          ·
            refine ⟨3961769042238545543578721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641179361492363695719147 3961769042238545543578721)
            ·
              refine ⟨2971326781678909157684041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3961769042238545543578721 2971326781678909157684041)
              ·
                refine ⟨2228495086259181868263031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971326781678909157684041 2228495086259181868263031)
                ·
                  refine ⟨3342742629388772802394547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228495086259181868263031 3342742629388772802394547)
                  ·
                    refine ⟨5014113944083159203591821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3342742629388772802394547 5014113944083159203591821)
                    ·
                      refine ⟨1880292729031184701346933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5014113944083159203591821 1880292729031184701346933)
                      ·
                        rfl

theorem cell23_3661857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_3661857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661857 prefixEnd_3661857 := by exact prefixLift 3661857
  have htrace : WordTrace (prefixWord ++ tailWord_3661857) baseStart_3661857 baseEnd_3661857 := by
    simpa [prefixWord, tailWord_3661857, baseEnd_3661857] using wordTrace_append hprefix tailTrace_3661857
  have hstable : (prefixWord ++ tailWord_3661857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661857).length < 2 ^ (prefixWord ++ tailWord_3661857).sum := by decide
  have hdescent : baseEnd_3661857 < baseStart_3661857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661886 : List Nat := [4, 2, 1, 3, 2, 1, 3, 7]
def baseStart_3661886 : Nat := 118140960795 + 3661886 * 2 ^ 59
def prefixEnd_3661886 : Nat := 4983230072969 + 3 ^ 40 * 3661886 * 2
def baseEnd_3661886 : Nat := 69641022961857966217937

theorem tailTrace_3661886 : CollatzResearch.WordTrace tailWord_3661886 prefixEnd_3661886 69641022961857966217937 := by
  unfold tailWord_3661886
  simp only [CollatzResearch.WordTrace]
  refine ⟨16694994351452487147905689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89039969874413264788830341 16694994351452487147905689)
  ·
    refine ⟨12521245763589365360929267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16694994351452487147905689 12521245763589365360929267)
    ·
      refine ⟨18781868645384048041393901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12521245763589365360929267 18781868645384048041393901)
      ·
        refine ⟨7043200742019018015522713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18781868645384048041393901 7043200742019018015522713)
        ·
          refine ⟨5282400556514263511642035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7043200742019018015522713 5282400556514263511642035)
          ·
            refine ⟨7923600834771395267463053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282400556514263511642035 7923600834771395267463053)
            ·
              refine ⟨2971350313039273225298645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7923600834771395267463053 2971350313039273225298645)
              ·
                refine ⟨69641022961857966217937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2971350313039273225298645 69641022961857966217937)
                ·
                  rfl

theorem cell23_3661886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_3661886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661886 prefixEnd_3661886 := by exact prefixLift 3661886
  have htrace : WordTrace (prefixWord ++ tailWord_3661886) baseStart_3661886 baseEnd_3661886 := by
    simpa [prefixWord, tailWord_3661886, baseEnd_3661886] using wordTrace_append hprefix tailTrace_3661886
  have hstable : (prefixWord ++ tailWord_3661886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661886).length < 2 ^ (prefixWord ++ tailWord_3661886).sum := by decide
  have hdescent : baseEnd_3661886 < baseStart_3661886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661912 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 2, 6]
def baseStart_3661912 : Nat := 118140960795 + 3661912 * 2 ^ 59
def prefixEnd_3661912 : Nat := 4983230072969 + 3 ^ 40 * 3661912 * 2
def baseEnd_3661912 : Nat := 626773656822393995386393

theorem tailTrace_3661912 : CollatzResearch.WordTrace tailWord_3661912 prefixEnd_3661912 626773656822393995386393 := by
  unfold tailWord_3661912
  simp only [CollatzResearch.WordTrace]
  refine ⟨66780451554762851811845995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89040602073017135749127993 66780451554762851811845995)
  ·
    refine ⟨100170677332144277717768993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66780451554762851811845995 100170677332144277717768993)
    ·
      refine ⟨75128007999108208288326745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100170677332144277717768993 75128007999108208288326745)
      ·
        refine ⟨56346005999331156216245059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75128007999108208288326745 56346005999331156216245059)
        ·
          refine ⟨84519008998996734324367589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56346005999331156216245059 84519008998996734324367589)
          ·
            refine ⟨15847314187311887685818923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84519008998996734324367589 15847314187311887685818923)
            ·
              refine ⟨23770971280967831528728385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15847314187311887685818923 23770971280967831528728385)
              ·
                refine ⟨17828228460725873646546289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23770971280967831528728385 17828228460725873646546289)
                ·
                  refine ⟨13371171345544405234909717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17828228460725873646546289 13371171345544405234909717)
                  ·
                    refine ⟨626773656822393995386393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13371171345544405234909717 626773656822393995386393)
                    ·
                      rfl

theorem cell23_3661912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_3661912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661912 prefixEnd_3661912 := by exact prefixLift 3661912
  have htrace : WordTrace (prefixWord ++ tailWord_3661912) baseStart_3661912 baseEnd_3661912 := by
    simpa [prefixWord, tailWord_3661912, baseEnd_3661912] using wordTrace_append hprefix tailTrace_3661912
  have hstable : (prefixWord ++ tailWord_3661912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661912).length < 2 ^ (prefixWord ++ tailWord_3661912).sum := by decide
  have hdescent : baseEnd_3661912 < baseStart_3661912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661930 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_3661930 : Nat := 118140960795 + 3661930 * 2 ^ 59
def prefixEnd_3661930 : Nat := 4983230072969 + 3 ^ 40 * 3661930 * 2
def baseEnd_3661930 : Nat := 1880330213118962915734097

theorem tailTrace_3661930 : CollatzResearch.WordTrace tailWord_3661930 prefixEnd_3661930 1880330213118962915734097 := by
  unfold tailWord_3661930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33390389905865123174461811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89041039748973661798564829 33390389905865123174461811)
  ·
    refine ⟨50085584858797684761692717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33390389905865123174461811 50085584858797684761692717)
    ·
      refine ⟨18782094322049131785634769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50085584858797684761692717 18782094322049131785634769)
      ·
        refine ⟨14086570741536848839226077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18782094322049131785634769 14086570741536848839226077)
        ·
          refine ⟨5282464028076318314709779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14086570741536848839226077 5282464028076318314709779)
          ·
            refine ⟨7923696042114477472064669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282464028076318314709779 7923696042114477472064669)
            ·
              refine ⟨2971386015792929052024251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7923696042114477472064669 2971386015792929052024251)
              ·
                refine ⟨4457079023689393578036377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971386015792929052024251 4457079023689393578036377)
                ·
                  refine ⟨3342809267767045183527283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457079023689393578036377 3342809267767045183527283)
                  ·
                    refine ⟨5014213901650567775290925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3342809267767045183527283 5014213901650567775290925)
                    ·
                      refine ⟨1880330213118962915734097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5014213901650567775290925 1880330213118962915734097)
                      ·
                        rfl

theorem cell23_3661930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_3661930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661930 prefixEnd_3661930 := by exact prefixLift 3661930
  have htrace : WordTrace (prefixWord ++ tailWord_3661930) baseStart_3661930 baseEnd_3661930 := by
    simpa [prefixWord, tailWord_3661930, baseEnd_3661930] using wordTrace_append hprefix tailTrace_3661930
  have hstable : (prefixWord ++ tailWord_3661930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661930).length < 2 ^ (prefixWord ++ tailWord_3661930).sum := by decide
  have hdescent : baseEnd_3661930 < baseStart_3661930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661936 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 1, 4, 2]
def baseStart_3661936 : Nat := 118140960795 + 3661936 * 2 ^ 59
def prefixEnd_3661936 : Nat := 4983230072969 + 3 ^ 40 * 3661936 * 2
def baseEnd_3661936 : Nat := 1880333294002889892259069

theorem tailTrace_3661936 : CollatzResearch.WordTrace tailWord_3661936 prefixEnd_3661936 1880333294002889892259069 := by
  unfold tailWord_3661936
  simp only [CollatzResearch.WordTrace]
  refine ⟨66780889230719377861282831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89041185640959170481710441 66780889230719377861282831)
  ·
    refine ⟨100171333846079066791924247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66780889230719377861282831 100171333846079066791924247)
    ·
      refine ⟨150257000769118600187886371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100171333846079066791924247 150257000769118600187886371)
      ·
        refine ⟨225385501153677900281829557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150257000769118600187886371 225385501153677900281829557)
        ·
          refine ⟨21129890733157303151421521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225385501153677900281829557 21129890733157303151421521)
          ·
            refine ⟨15847418049867977363566141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21129890733157303151421521 15847418049867977363566141)
            ·
              refine ⟨5942781768700491511337303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15847418049867977363566141 5942781768700491511337303)
              ·
                refine ⟨8914172653050737267005955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942781768700491511337303 8914172653050737267005955)
                ·
                  refine ⟨13371258979576105900508933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8914172653050737267005955 13371258979576105900508933)
                  ·
                    refine ⟨2507111058670519856345425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13371258979576105900508933 2507111058670519856345425)
                    ·
                      refine ⟨1880333294002889892259069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507111058670519856345425 1880333294002889892259069)
                      ·
                        rfl

theorem cell23_3661936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 4, 2].length) (baseStart_3661936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661936 prefixEnd_3661936 := by exact prefixLift 3661936
  have htrace : WordTrace (prefixWord ++ tailWord_3661936) baseStart_3661936 baseEnd_3661936 := by
    simpa [prefixWord, tailWord_3661936, baseEnd_3661936] using wordTrace_append hprefix tailTrace_3661936
  have hstable : (prefixWord ++ tailWord_3661936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661936).length < 2 ^ (prefixWord ++ tailWord_3661936).sum := by decide
  have hdescent : baseEnd_3661936 < baseStart_3661936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661976 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 7]
def baseStart_3661976 : Nat := 118140960795 + 3661976 * 2 ^ 59
def prefixEnd_3661976 : Nat := 4983230072969 + 3 ^ 40 * 3661976 * 2
def baseEnd_3661976 : Nat := 208928203692118859528765

theorem tailTrace_3661976 : CollatzResearch.WordTrace tailWord_3661976 prefixEnd_3661976 208928203692118859528765 := by
  unfold tailWord_3661976
  simp only [CollatzResearch.WordTrace]
  refine ⟨66781618690646921277010891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89042158254195895036014521 66781618690646921277010891)
  ·
    refine ⟨100172428035970381915516337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66781618690646921277010891 100172428035970381915516337)
    ·
      refine ⟨75129321026977786436637253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100172428035970381915516337 75129321026977786436637253)
      ·
        refine ⟨14086747692558334956869485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75129321026977786436637253 14086747692558334956869485)
        ·
          refine ⟨5282530384709375608826057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14086747692558334956869485 5282530384709375608826057)
          ·
            refine ⟨3961897788532031706619543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5282530384709375608826057 3961897788532031706619543)
            ·
              refine ⟨5942846682798047559929315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961897788532031706619543 5942846682798047559929315)
              ·
                refine ⟨8914270024197071339893973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942846682798047559929315 8914270024197071339893973)
                ·
                  refine ⟨208928203692118859528765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8914270024197071339893973 208928203692118859528765)
                  ·
                    rfl

theorem cell23_3661976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 7].length) (baseStart_3661976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3661976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3661976 prefixEnd_3661976 := by exact prefixLift 3661976
  have htrace : WordTrace (prefixWord ++ tailWord_3661976) baseStart_3661976 baseEnd_3661976 := by
    simpa [prefixWord, tailWord_3661976, baseEnd_3661976] using wordTrace_append hprefix tailTrace_3661976
  have hstable : (prefixWord ++ tailWord_3661976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661976).length < 2 ^ (prefixWord ++ tailWord_3661976).sum := by decide
  have hdescent : baseEnd_3661976 < baseStart_3661976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662026 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2]
def baseStart_3662026 : Nat := 118140960795 + 3662026 * 2 ^ 59
def prefixEnd_3662026 : Nat := 4983230072969 + 3 ^ 40 * 3662026 * 2
def baseEnd_3662026 : Nat := 1880379507261794540133655

theorem tailTrace_3662026 : CollatzResearch.WordTrace tailWord_3662026 prefixEnd_3662026 1880379507261794540133655 := by
  unfold tailWord_3662026
  simp only [CollatzResearch.WordTrace]
  refine ⟨33391265257778175273335483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89043374020741800728894621 33391265257778175273335483)
  ·
    refine ⟨50086897886667262910003225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33391265257778175273335483 50086897886667262910003225)
    ·
      refine ⟨37565173415000447182502419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50086897886667262910003225 37565173415000447182502419)
      ·
        refine ⟨56347760122500670773753629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37565173415000447182502419 56347760122500670773753629)
        ·
          refine ⟨21130410045937751540157611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56347760122500670773753629 21130410045937751540157611)
          ·
            refine ⟨31695615068906627310236417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21130410045937751540157611 31695615068906627310236417)
            ·
              refine ⟨23771711301679970482677313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31695615068906627310236417 23771711301679970482677313)
              ·
                refine ⟨17828783476259977862007985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23771711301679970482677313 17828783476259977862007985)
                ·
                  refine ⟨13371587607194983396505989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17828783476259977862007985 13371587607194983396505989)
                  ·
                    refine ⟨2507172676349059386844873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13371587607194983396505989 2507172676349059386844873)
                    ·
                      refine ⟨1880379507261794540133655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507172676349059386844873 1880379507261794540133655)
                      ·
                        rfl

theorem cell23_3662026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_3662026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662026 prefixEnd_3662026 := by exact prefixLift 3662026
  have htrace : WordTrace (prefixWord ++ tailWord_3662026) baseStart_3662026 baseEnd_3662026 := by
    simpa [prefixWord, tailWord_3662026, baseEnd_3662026] using wordTrace_append hprefix tailTrace_3662026
  have hstable : (prefixWord ++ tailWord_3662026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662026).length < 2 ^ (prefixWord ++ tailWord_3662026).sum := by decide
  have hdescent : baseEnd_3662026 < baseStart_3662026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662049 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 6]
def baseStart_3662049 : Nat := 118140960795 + 3662049 * 2 ^ 59
def prefixEnd_3662049 : Nat := 4983230072969 + 3 ^ 40 * 3662049 * 2
def baseEnd_3662049 : Nat := 208932368590760883349561

theorem tailTrace_3662049 : CollatzResearch.WordTrace tailWord_3662049 prefixEnd_3662049 208932368590760883349561 := by
  unfold tailWord_3662049
  simp only [CollatzResearch.WordTrace]
  refine ⟨133565899910029376021429201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89043933273352917347619467 133565899910029376021429201)
  ·
    refine ⟨100174424932522032016071901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133565899910029376021429201 100174424932522032016071901)
    ·
      refine ⟨37565409349695762006026963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100174424932522032016071901 37565409349695762006026963)
      ·
        refine ⟨56348114024543643009040445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37565409349695762006026963 56348114024543643009040445)
        ·
          refine ⟨21130542759203866128390167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56348114024543643009040445 21130542759203866128390167)
          ·
            refine ⟨31695814138805799192585251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21130542759203866128390167 31695814138805799192585251)
            ·
              refine ⟨47543721208208698788877877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31695814138805799192585251 47543721208208698788877877)
              ·
                refine ⟨4457223863269565511457301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47543721208208698788877877 4457223863269565511457301)
                ·
                  refine ⟨208932368590760883349561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4457223863269565511457301 208932368590760883349561)
                  ·
                    rfl

theorem cell23_3662049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 6].length) (baseStart_3662049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662049 prefixEnd_3662049 := by exact prefixLift 3662049
  have htrace : WordTrace (prefixWord ++ tailWord_3662049) baseStart_3662049 baseEnd_3662049 := by
    simpa [prefixWord, tailWord_3662049, baseEnd_3662049] using wordTrace_append hprefix tailTrace_3662049
  have hstable : (prefixWord ++ tailWord_3662049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662049).length < 2 ^ (prefixWord ++ tailWord_3662049).sum := by decide
  have hdescent : baseEnd_3662049 < baseStart_3662049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662063 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 3]
def baseStart_3662063 : Nat := 118140960795 + 3662063 * 2 ^ 59
def prefixEnd_3662063 : Nat := 4983230072969 + 3 ^ 40 * 3662063 * 2
def baseEnd_3662063 : Nat := 1880398506046010895370985

theorem tailTrace_3662063 : CollatzResearch.WordTrace tailWord_3662063 prefixEnd_3662063 1880398506046010895370985 := by
  unfold tailWord_3662063
  simp only [CollatzResearch.WordTrace]
  refine ⟨133566410531978656412438843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89044273687985770941625895 133566410531978656412438843)
  ·
    refine ⟨200349615797967984618658265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133566410531978656412438843 200349615797967984618658265)
    ·
      refine ⟨150262211848475988463993699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200349615797967984618658265 150262211848475988463993699)
      ·
        refine ⟨225393317772713982695990549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150262211848475988463993699 225393317772713982695990549)
        ·
          refine ⟨10565311770595967938874557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225393317772713982695990549 10565311770595967938874557)
          ·
            refine ⟨3961991913973487977077959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10565311770595967938874557 3961991913973487977077959)
            ·
              refine ⟨5942987870960231965616939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961991913973487977077959 5942987870960231965616939)
              ·
                refine ⟨8914481806440347948425409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942987870960231965616939 8914481806440347948425409)
                ·
                  refine ⟨6685861354830260961319057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8914481806440347948425409 6685861354830260961319057)
                  ·
                    refine ⟨5014396016122695720989293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6685861354830260961319057 5014396016122695720989293)
                    ·
                      refine ⟨1880398506046010895370985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5014396016122695720989293 1880398506046010895370985)
                      ·
                        rfl

theorem cell23_3662063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 3].length) (baseStart_3662063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662063 prefixEnd_3662063 := by exact prefixLift 3662063
  have htrace : WordTrace (prefixWord ++ tailWord_3662063) baseStart_3662063 baseEnd_3662063 := by
    simpa [prefixWord, tailWord_3662063, baseEnd_3662063] using wordTrace_append hprefix tailTrace_3662063
  have hstable : (prefixWord ++ tailWord_3662063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662063).length < 2 ^ (prefixWord ++ tailWord_3662063).sum := by decide
  have hdescent : baseEnd_3662063 < baseStart_3662063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662099 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 4]
def baseStart_3662099 : Nat := 118140960795 + 3662099 * 2 ^ 59
def prefixEnd_3662099 : Nat := 4983230072969 + 3 ^ 40 * 3662099 * 2
def baseEnd_3662099 : Nat := 1880416991349572754520819

theorem tailTrace_3662099 : CollatzResearch.WordTrace tailWord_3662099 prefixEnd_3662099 1880416991349572754520819 := by
  unfold tailWord_3662099
  simp only [CollatzResearch.WordTrace]
  refine ⟨133567723559848234560749351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89045149039898823040499567 133567723559848234560749351)
  ·
    refine ⟨200351585339772351841124027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133567723559848234560749351 200351585339772351841124027)
    ·
      refine ⟨300527378009658527761686041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200351585339772351841124027 300527378009658527761686041)
      ·
        refine ⟨225395533507243895821264531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300527378009658527761686041 225395533507243895821264531)
        ·
          refine ⟨338093300260865843731896797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225395533507243895821264531 338093300260865843731896797)
          ·
            refine ⟨126784987597824691399461299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338093300260865843731896797 126784987597824691399461299)
            ·
              refine ⟨190177481396737037099191949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126784987597824691399461299 190177481396737037099191949)
              ·
                refine ⟨71316555523776388912196981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190177481396737037099191949 71316555523776388912196981)
                ·
                  refine ⟨6685927080354036460518467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71316555523776388912196981 6685927080354036460518467)
                  ·
                    refine ⟨10028890620531054690777701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6685927080354036460518467 10028890620531054690777701)
                    ·
                      refine ⟨1880416991349572754520819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10028890620531054690777701 1880416991349572754520819)
                      ·
                        rfl

theorem cell23_3662099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_3662099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662099 prefixEnd_3662099 := by exact prefixLift 3662099
  have htrace : WordTrace (prefixWord ++ tailWord_3662099) baseStart_3662099 baseEnd_3662099 := by
    simpa [prefixWord, tailWord_3662099, baseEnd_3662099] using wordTrace_append hprefix tailTrace_3662099
  have hstable : (prefixWord ++ tailWord_3662099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662099).length < 2 ^ (prefixWord ++ tailWord_3662099).sum := by decide
  have hdescent : baseEnd_3662099 < baseStart_3662099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662160 : List Nat := [2, 1, 1, 1, 1, 8, 2, 1, 2, 4]
def baseStart_3662160 : Nat := 118140960795 + 3662160 * 2 ^ 59
def prefixEnd_3662160 : Nat := 4983230072969 + 3 ^ 40 * 3662160 * 2
def baseEnd_3662160 : Nat := 626816104556499005286013

theorem tailTrace_3662160 : CollatzResearch.WordTrace tailWord_3662160 prefixEnd_3662160 626816104556499005286013 := by
  unfold tailWord_3662160
  simp only [CollatzResearch.WordTrace]
  refine ⟨66784974206313620989359967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89046632275084827985813289 66784974206313620989359967)
  ·
    refine ⟨100177461309470431484039951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66784974206313620989359967 100177461309470431484039951)
    ·
      refine ⟨150266191964205647226059927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100177461309470431484039951 150266191964205647226059927)
      ·
        refine ⟨225399287946308470839089891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150266191964205647226059927 225399287946308470839089891)
        ·
          refine ⟨338098931919462706258634837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225399287946308470839089891 338098931919462706258634837)
          ·
            refine ⟨3962096858431203588968377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 338098931919462706258634837 3962096858431203588968377)
            ·
              refine ⟨2971572643823402691726283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3962096858431203588968377 2971572643823402691726283)
              ·
                refine ⟨4457358965735104037589425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971572643823402691726283 4457358965735104037589425)
                ·
                  refine ⟨3343019224301328028192069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457358965735104037589425 3343019224301328028192069)
                  ·
                    refine ⟨626816104556499005286013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3343019224301328028192069 626816104556499005286013)
                    ·
                      rfl

theorem cell23_3662160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 4].length) (baseStart_3662160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662160 prefixEnd_3662160 := by exact prefixLift 3662160
  have htrace : WordTrace (prefixWord ++ tailWord_3662160) baseStart_3662160 baseEnd_3662160 := by
    simpa [prefixWord, tailWord_3662160, baseEnd_3662160] using wordTrace_append hprefix tailTrace_3662160
  have hstable : (prefixWord ++ tailWord_3662160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662160).length < 2 ^ (prefixWord ++ tailWord_3662160).sum := by decide
  have hdescent : baseEnd_3662160 < baseStart_3662160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662183 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_3662183 : Nat := 118140960795 + 3662183 * 2 ^ 59
def prefixEnd_3662183 : Nat := 4983230072969 + 3 ^ 40 * 3662183 * 2
def baseEnd_3662183 : Nat := 1880460123724550425870433

theorem tailTrace_3662183 : CollatzResearch.WordTrace tailWord_3662183 prefixEnd_3662183 1880460123724550425870433 := by
  unfold tailWord_3662183
  simp only [CollatzResearch.WordTrace]
  refine ⟨133570787291543916906807203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89047191527695944604538135 133570787291543916906807203)
  ·
    refine ⟨200356180937315875360210805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133570787291543916906807203 200356180937315875360210805)
    ·
      refine ⟨18783391962873363315019763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200356180937315875360210805 18783391962873363315019763)
      ·
        refine ⟨28175087944310044972529645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18783391962873363315019763 28175087944310044972529645)
        ·
          refine ⟨10565657979116266864698617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28175087944310044972529645 10565657979116266864698617)
          ·
            refine ⟨7924243484337200148523963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10565657979116266864698617 7924243484337200148523963)
            ·
              refine ⟨11886365226505800222785945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924243484337200148523963 11886365226505800222785945)
              ·
                refine ⟨8914773919879350167089459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11886365226505800222785945 8914773919879350167089459)
                ·
                  refine ⟨13372160879819025250634189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8914773919879350167089459 13372160879819025250634189)
                  ·
                    refine ⟨5014560329932134468987821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13372160879819025250634189 5014560329932134468987821)
                    ·
                      refine ⟨1880460123724550425870433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5014560329932134468987821 1880460123724550425870433)
                      ·
                        rfl

theorem cell23_3662183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_3662183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662183 prefixEnd_3662183 := by exact prefixLift 3662183
  have htrace : WordTrace (prefixWord ++ tailWord_3662183) baseStart_3662183 baseEnd_3662183 := by
    simpa [prefixWord, tailWord_3662183, baseEnd_3662183] using wordTrace_append hprefix tailTrace_3662183
  have hstable : (prefixWord ++ tailWord_3662183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662183).length < 2 ^ (prefixWord ++ tailWord_3662183).sum := by decide
  have hdescent : baseEnd_3662183 < baseStart_3662183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662216 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 2, 6]
def baseStart_3662216 : Nat := 118140960795 + 3662216 * 2 ^ 59
def prefixEnd_3662216 : Nat := 4983230072969 + 3 ^ 40 * 3662216 * 2
def baseEnd_3662216 : Nat := 626825689528716265585927

theorem tailTrace_3662216 : CollatzResearch.WordTrace tailWord_3662216 prefixEnd_3662216 626825689528716265585927 := by
  unfold tailWord_3662216
  simp only [CollatzResearch.WordTrace]
  refine ⟨66785995450212181771379251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89047993933616242361839001 66785995450212181771379251)
  ·
    refine ⟨100178993175318272657068877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66785995450212181771379251 100178993175318272657068877)
    ·
      refine ⟨37567122440744352246400829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100178993175318272657068877 37567122440744352246400829)
      ·
        refine ⟨14087670915279132092400311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37567122440744352246400829 14087670915279132092400311)
        ·
          refine ⟨21131506372918698138600467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14087670915279132092400311 21131506372918698138600467)
          ·
            refine ⟨31697259559378047207900701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21131506372918698138600467 31697259559378047207900701)
            ·
              refine ⟨11886472334766767702962763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31697259559378047207900701 11886472334766767702962763)
              ·
                refine ⟨17829708502150151554444145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11886472334766767702962763 17829708502150151554444145)
                ·
                  refine ⟨13372281376612613665833109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17829708502150151554444145 13372281376612613665833109)
                  ·
                    refine ⟨626825689528716265585927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13372281376612613665833109 626825689528716265585927)
                    ·
                      rfl

theorem cell23_3662216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_3662216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662216 prefixEnd_3662216 := by exact prefixLift 3662216
  have htrace : WordTrace (prefixWord ++ tailWord_3662216) baseStart_3662216 baseEnd_3662216 := by
    simpa [prefixWord, tailWord_3662216, baseEnd_3662216] using wordTrace_append hprefix tailTrace_3662216
  have hstable : (prefixWord ++ tailWord_3662216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662216).length < 2 ^ (prefixWord ++ tailWord_3662216).sum := by decide
  have hdescent : baseEnd_3662216 < baseStart_3662216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662257 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 2, 2, 2]
def baseStart_3662257 : Nat := 118140960795 + 3662257 * 2 ^ 59
def prefixEnd_3662257 : Nat := 4983230072969 + 3 ^ 40 * 3662257 * 2
def baseEnd_3662257 : Nat := 1880498121292983136345093

theorem tailTrace_3662257 : CollatzResearch.WordTrace tailWord_3662257 prefixEnd_3662257 1880498121292983136345093 := by
  unfold tailWord_3662257
  simp only [CollatzResearch.WordTrace]
  refine ⟨133573486293275827545001025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89048990862183885030000683 133573486293275827545001025)
  ·
    refine ⟨100180114719956870658750769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133573486293275827545001025 100180114719956870658750769)
    ·
      refine ⟨75135086039967652994063077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100180114719956870658750769 75135086039967652994063077)
      ·
        refine ⟨14087828632493934936386827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75135086039967652994063077 14087828632493934936386827)
        ·
          refine ⟨21131742948740902404580241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14087828632493934936386827 21131742948740902404580241)
          ·
            refine ⟨15848807211555676803435181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21131742948740902404580241 15848807211555676803435181)
            ·
              refine ⟨5943302704333378801288193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15848807211555676803435181 5943302704333378801288193)
              ·
                refine ⟨4457477028250034100966145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5943302704333378801288193 4457477028250034100966145)
                ·
                  refine ⟨3343107771187525575724609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457477028250034100966145 3343107771187525575724609)
                  ·
                    refine ⟨2507330828390644181793457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3343107771187525575724609 2507330828390644181793457)
                    ·
                      refine ⟨1880498121292983136345093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507330828390644181793457 1880498121292983136345093)
                      ·
                        rfl

theorem cell23_3662257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_3662257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662257 prefixEnd_3662257 := by exact prefixLift 3662257
  have htrace : WordTrace (prefixWord ++ tailWord_3662257) baseStart_3662257 baseEnd_3662257 := by
    simpa [prefixWord, tailWord_3662257, baseEnd_3662257] using wordTrace_append hprefix tailTrace_3662257
  have hstable : (prefixWord ++ tailWord_3662257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662257).length < 2 ^ (prefixWord ++ tailWord_3662257).sum := by decide
  have hdescent : baseEnd_3662257 < baseStart_3662257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662263 : List Nat := [1, 1, 3, 1, 3, 3, 2, 4, 5]
def baseStart_3662263 : Nat := 118140960795 + 3662263 * 2 ^ 59
def prefixEnd_3662263 : Nat := 4983230072969 + 3 ^ 40 * 3662263 * 2
def baseEnd_3662263 : Nat := 208944578019656679207785

theorem tailTrace_3662263 : CollatzResearch.WordTrace tailWord_3662263 prefixEnd_3662263 208944578019656679207785 := by
  unfold tailWord_3662263
  simp only [CollatzResearch.WordTrace]
  refine ⟨133573705131254090569719443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89049136754169393713146295 133573705131254090569719443)
  ·
    refine ⟨200360557696881135854579165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133573705131254090569719443 200360557696881135854579165)
    ·
      refine ⟨75135209136330425945467187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200360557696881135854579165 75135209136330425945467187)
      ·
        refine ⟨112702813704495638918200781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75135209136330425945467187 112702813704495638918200781)
        ·
          refine ⟨42263555139185864594325293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112702813704495638918200781 42263555139185864594325293)
          ·
            refine ⟨15848833177194699222871985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42263555139185864594325293 15848833177194699222871985)
            ·
              refine ⟨11886624882896024417153989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15848833177194699222871985 11886624882896024417153989)
              ·
                refine ⟨2228742165543004578216373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11886624882896024417153989 2228742165543004578216373)
                ·
                  refine ⟨208944578019656679207785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2228742165543004578216373 208944578019656679207785)
                  ·
                    rfl

theorem cell23_3662263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 5].length) (baseStart_3662263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662263 prefixEnd_3662263 := by exact prefixLift 3662263
  have htrace : WordTrace (prefixWord ++ tailWord_3662263) baseStart_3662263 baseEnd_3662263 := by
    simpa [prefixWord, tailWord_3662263, baseEnd_3662263] using wordTrace_append hprefix tailTrace_3662263
  have hstable : (prefixWord ++ tailWord_3662263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662263).length < 2 ^ (prefixWord ++ tailWord_3662263).sum := by decide
  have hdescent : baseEnd_3662263 < baseStart_3662263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662286 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3662286 : Nat := 118140960795 + 3662286 * 2 ^ 59
def prefixEnd_3662286 : Nat := 4983230072969 + 3 ^ 40 * 3662286 * 2
def baseEnd_3662286 : Nat := 1880513012231963522882459

theorem tailTrace_3662286 : CollatzResearch.WordTrace tailWord_3662286 prefixEnd_3662286 1880513012231963522882459 := by
  unfold tailWord_3662286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16696818001271345687225839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89049696006780510331871141 16696818001271345687225839)
  ·
    refine ⟨25045227001907018530838759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16696818001271345687225839 25045227001907018530838759)
    ·
      refine ⟨37567840502860527796258139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25045227001907018530838759 37567840502860527796258139)
      ·
        refine ⟨56351760754290791694387209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37567840502860527796258139 56351760754290791694387209)
        ·
          refine ⟨42263820565718093770790407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56351760754290791694387209 42263820565718093770790407)
          ·
            refine ⟨63395730848577140656185611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42263820565718093770790407 63395730848577140656185611)
            ·
              refine ⟨95093596272865710984278417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63395730848577140656185611 95093596272865710984278417)
              ·
                refine ⟨71320197204649283238208813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95093596272865710984278417 71320197204649283238208813)
                ·
                  refine ⟨26745073951743481214328305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71320197204649283238208813 26745073951743481214328305)
                  ·
                    refine ⟨20058805463807610910746229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26745073951743481214328305 20058805463807610910746229)
                    ·
                      refine ⟨1880513012231963522882459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20058805463807610910746229 1880513012231963522882459)
                      ·
                        rfl

theorem cell23_3662286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3662286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662286 prefixEnd_3662286 := by exact prefixLift 3662286
  have htrace : WordTrace (prefixWord ++ tailWord_3662286) baseStart_3662286 baseEnd_3662286 := by
    simpa [prefixWord, tailWord_3662286, baseEnd_3662286] using wordTrace_append hprefix tailTrace_3662286
  have hstable : (prefixWord ++ tailWord_3662286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662286).length < 2 ^ (prefixWord ++ tailWord_3662286).sum := by decide
  have hdescent : baseEnd_3662286 < baseStart_3662286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662313 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 2, 4, 2]
def baseStart_3662313 : Nat := 118140960795 + 3662313 * 2 ^ 59
def prefixEnd_3662313 : Nat := 4983230072969 + 3 ^ 40 * 3662313 * 2
def baseEnd_3662313 : Nat := 1880526876209634917244835

theorem tailTrace_3662313 : CollatzResearch.WordTrace tailWord_3662313 prefixEnd_3662313 1880526876209634917244835 := by
  unfold tailWord_3662313
  simp only [CollatzResearch.WordTrace]
  refine ⟨133575528781072949109039593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89050352520715299406026395 133575528781072949109039593)
  ·
    refine ⟨100181646585804711831779695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133575528781072949109039593 100181646585804711831779695)
    ·
      refine ⟨150272469878707067747669543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100181646585804711831779695 150272469878707067747669543)
      ·
        refine ⟨225408704818060601621504315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150272469878707067747669543 225408704818060601621504315)
        ·
          refine ⟨338113057227090902432256473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225408704818060601621504315 338113057227090902432256473)
          ·
            refine ⟨253584792920318176824192355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338113057227090902432256473 253584792920318176824192355)
            ·
              refine ⟨380377189380477265236288533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253584792920318176824192355 380377189380477265236288533)
              ·
                refine ⟨17830180752209871807951025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 380377189380477265236288533 17830180752209871807951025)
                ·
                  refine ⟨13372635564157403855963269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17830180752209871807951025 13372635564157403855963269)
                  ·
                    refine ⟨2507369168279513222993113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13372635564157403855963269 2507369168279513222993113)
                    ·
                      refine ⟨1880526876209634917244835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507369168279513222993113 1880526876209634917244835)
                      ·
                        rfl

theorem cell23_3662313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 4, 2].length) (baseStart_3662313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662313 prefixEnd_3662313 := by exact prefixLift 3662313
  have htrace : WordTrace (prefixWord ++ tailWord_3662313) baseStart_3662313 baseEnd_3662313 := by
    simpa [prefixWord, tailWord_3662313, baseEnd_3662313] using wordTrace_append hprefix tailTrace_3662313
  have hstable : (prefixWord ++ tailWord_3662313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662313).length < 2 ^ (prefixWord ++ tailWord_3662313).sum := by decide
  have hdescent : baseEnd_3662313 < baseStart_3662313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662333 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_3662333 : Nat := 118140960795 + 3662333 * 2 ^ 59
def prefixEnd_3662333 : Nat := 4983230072969 + 3 ^ 40 * 3662333 * 2
def baseEnd_3662333 : Nat := 1880537145822724838994743

theorem tailTrace_3662333 : CollatzResearch.WordTrace tailWord_3662333 prefixEnd_3662333 1880537145822724838994743 := by
  unfold tailWord_3662333
  simp only [CollatzResearch.WordTrace]
  refine ⟨133576258241000492524767653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89050838827333661683178435 133576258241000492524767653)
  ·
    refine ⟨25045548420187592348393935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133576258241000492524767653 25045548420187592348393935)
    ·
      refine ⟨37568322630281388522590903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25045548420187592348393935 37568322630281388522590903)
      ·
        refine ⟨56352483945422082783886355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37568322630281388522590903 56352483945422082783886355)
        ·
          refine ⟨84528725918133124175829533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56352483945422082783886355 84528725918133124175829533)
          ·
            refine ⟨31698272219299921565936075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84528725918133124175829533 31698272219299921565936075)
            ·
              refine ⟨47547408328949882348904113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31698272219299921565936075 47547408328949882348904113)
              ·
                refine ⟨35660556246712411761678085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47547408328949882348904113 35660556246712411761678085)
                ·
                  refine ⟨6686354296258577205314641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35660556246712411761678085 6686354296258577205314641)
                  ·
                    refine ⟨5014765722193932903985981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6686354296258577205314641 5014765722193932903985981)
                    ·
                      refine ⟨1880537145822724838994743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5014765722193932903985981 1880537145822724838994743)
                      ·
                        rfl

theorem cell23_3662333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_3662333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662333 prefixEnd_3662333 := by exact prefixLift 3662333
  have htrace : WordTrace (prefixWord ++ tailWord_3662333) baseStart_3662333 baseEnd_3662333 := by
    simpa [prefixWord, tailWord_3662333, baseEnd_3662333] using wordTrace_append hprefix tailTrace_3662333
  have hstable : (prefixWord ++ tailWord_3662333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662333).length < 2 ^ (prefixWord ++ tailWord_3662333).sum := by decide
  have hdescent : baseEnd_3662333 < baseStart_3662333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662350 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3662350 : Nat := 118140960795 + 3662350 * 2 ^ 59
def prefixEnd_3662350 : Nat := 4983230072969 + 3 ^ 40 * 3662350 * 2
def baseEnd_3662350 : Nat := 1880545874993851272482165

theorem tailTrace_3662350 : CollatzResearch.WordTrace tailWord_3662350 prefixEnd_3662350 1880545874993851272482165 := by
  unfold tailWord_3662350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16697109785242363053517063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89051252187959269618757669 16697109785242363053517063)
  ·
    refine ⟨25045664677863544580275595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16697109785242363053517063 25045664677863544580275595)
    ·
      refine ⟨37568497016795316870413393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25045664677863544580275595 37568497016795316870413393)
      ·
        refine ⟨28176372762596487652810045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37568497016795316870413393 28176372762596487652810045)
        ·
          refine ⟨10566139785973682869803767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28176372762596487652810045 10566139785973682869803767)
          ·
            refine ⟨15849209678960524304705651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10566139785973682869803767 15849209678960524304705651)
            ·
              refine ⟨23773814518440786457058477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15849209678960524304705651 23773814518440786457058477)
              ·
                refine ⟨8915180444415294921396929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23773814518440786457058477 8915180444415294921396929)
                ·
                  refine ⟨6686385333311471191047697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8915180444415294921396929 6686385333311471191047697)
                  ·
                    refine ⟨5014788999983603393285773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6686385333311471191047697 5014788999983603393285773)
                    ·
                      refine ⟨1880545874993851272482165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5014788999983603393285773 1880545874993851272482165)
                      ·
                        rfl

theorem cell23_3662350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3662350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662350 prefixEnd_3662350 := by exact prefixLift 3662350
  have htrace : WordTrace (prefixWord ++ tailWord_3662350) baseStart_3662350 baseEnd_3662350 := by
    simpa [prefixWord, tailWord_3662350, baseEnd_3662350] using wordTrace_append hprefix tailTrace_3662350
  have hstable : (prefixWord ++ tailWord_3662350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662350).length < 2 ^ (prefixWord ++ tailWord_3662350).sum := by decide
  have hdescent : baseEnd_3662350 < baseStart_3662350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662381 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3662381 : Nat := 118140960795 + 3662381 * 2 ^ 59
def prefixEnd_3662381 : Nat := 4983230072969 + 3 ^ 40 * 3662381 * 2
def baseEnd_3662381 : Nat := 1880561792894140651194523

theorem tailTrace_3662381 : CollatzResearch.WordTrace tailWord_3662381 prefixEnd_3662381 1880561792894140651194523 := by
  unfold tailWord_3662381
  simp only [CollatzResearch.WordTrace]
  refine ⟨133578008944826596722514997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89052005963217731148343331 133578008944826596722514997)
  ·
    refine ⟨12522938338577493442735781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133578008944826596722514997 12522938338577493442735781)
    ·
      refine ⟨2348050938483280020512959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12522938338577493442735781 2348050938483280020512959)
      ·
        refine ⟨3522076407724920030769439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348050938483280020512959 3522076407724920030769439)
        ·
          refine ⟨5283114611587380046154159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522076407724920030769439 5283114611587380046154159)
          ·
            refine ⟨7924671917381070069231239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283114611587380046154159 7924671917381070069231239)
            ·
              refine ⟨11887007876071605103846859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924671917381070069231239 11887007876071605103846859)
              ·
                refine ⟨17830511814107407655770289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11887007876071605103846859 17830511814107407655770289)
                ·
                  refine ⟨13372883860580555741827717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17830511814107407655770289 13372883860580555741827717)
                  ·
                    refine ⟨2507415723858854201592697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13372883860580555741827717 2507415723858854201592697)
                    ·
                      refine ⟨1880561792894140651194523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507415723858854201592697 1880561792894140651194523)
                      ·
                        rfl

theorem cell23_3662381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3662381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662381 prefixEnd_3662381 := by exact prefixLift 3662381
  have htrace : WordTrace (prefixWord ++ tailWord_3662381) baseStart_3662381 baseEnd_3662381 := by
    simpa [prefixWord, tailWord_3662381, baseEnd_3662381] using wordTrace_append hprefix tailTrace_3662381
  have hstable : (prefixWord ++ tailWord_3662381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662381).length < 2 ^ (prefixWord ++ tailWord_3662381).sum := by decide
  have hdescent : baseEnd_3662381 < baseStart_3662381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662397 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3662397 : Nat := 118140960795 + 3662397 * 2 ^ 59
def prefixEnd_3662397 : Nat := 4983230072969 + 3 ^ 40 * 3662397 * 2
def baseEnd_3662397 : Nat := 1880570008584612588594449

theorem tailTrace_3662397 : CollatzResearch.WordTrace tailWord_3662397 prefixEnd_3662397 1880570008584612588594449 := by
  unfold tailWord_3662397
  simp only [CollatzResearch.WordTrace]
  refine ⟨133578592512768631455097445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89052395008512420970064963 133578592512768631455097445)
  ·
    refine ⟨25045986096144118397830771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133578592512768631455097445 25045986096144118397830771)
    ·
      refine ⟨37568979144216177596746157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25045986096144118397830771 37568979144216177596746157)
      ·
        refine ⟨14088367179081066598779809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37568979144216177596746157 14088367179081066598779809)
        ·
          refine ⟨10566275384310799949084857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14088367179081066598779809 10566275384310799949084857)
          ·
            refine ⟨7924706538233099961813643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10566275384310799949084857 7924706538233099961813643)
            ·
              refine ⟨11887059807349649942720465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924706538233099961813643 11887059807349649942720465)
              ·
                refine ⟨8915294855512237457040349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887059807349649942720465 8915294855512237457040349)
                ·
                  refine ⟨3343235570817089046390131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8915294855512237457040349 3343235570817089046390131)
                  ·
                    refine ⟨5014853356225633569585197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3343235570817089046390131 5014853356225633569585197)
                    ·
                      refine ⟨1880570008584612588594449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5014853356225633569585197 1880570008584612588594449)
                      ·
                        rfl

theorem cell23_3662397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3662397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662397 prefixEnd_3662397 := by exact prefixLift 3662397
  have htrace : WordTrace (prefixWord ++ tailWord_3662397) baseStart_3662397 baseEnd_3662397 := by
    simpa [prefixWord, tailWord_3662397, baseEnd_3662397] using wordTrace_append hprefix tailTrace_3662397
  have hstable : (prefixWord ++ tailWord_3662397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662397).length < 2 ^ (prefixWord ++ tailWord_3662397).sum := by decide
  have hdescent : baseEnd_3662397 < baseStart_3662397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662407 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_3662407 : Nat := 118140960795 + 3662407 * 2 ^ 59
def prefixEnd_3662407 : Nat := 4983230072969 + 3 ^ 40 * 3662407 * 2
def baseEnd_3662407 : Nat := 1880575143391157549469403

theorem tailTrace_3662407 : CollatzResearch.WordTrace tailWord_3662407 prefixEnd_3662407 1880575143391157549469403 := by
  unfold tailWord_3662407
  simp only [CollatzResearch.WordTrace]
  refine ⟨133578957242732403162961475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89052638161821602108640983 133578957242732403162961475)
  ·
    refine ⟨200368435864098604744442213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133578957242732403162961475 200368435864098604744442213)
    ·
      refine ⟨37569081724518488389582915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200368435864098604744442213 37569081724518488389582915)
      ·
        refine ⟨56353622586777732584374373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37569081724518488389582915 56353622586777732584374373)
        ·
          refine ⟨10566304235020824859570195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56353622586777732584374373 10566304235020824859570195)
          ·
            refine ⟨15849456352531237289355293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10566304235020824859570195 15849456352531237289355293)
            ·
              refine ⟨5943546132199213983508235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15849456352531237289355293 5943546132199213983508235)
              ·
                refine ⟨8915319198298820975262353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5943546132199213983508235 8915319198298820975262353)
                ·
                  refine ⟨6686489398724115731446765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8915319198298820975262353 6686489398724115731446765)
                  ·
                    refine ⟨2507433524521543399292537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6686489398724115731446765 2507433524521543399292537)
                    ·
                      refine ⟨1880575143391157549469403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507433524521543399292537 1880575143391157549469403)
                      ·
                        rfl

theorem cell23_3662407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_3662407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662407 prefixEnd_3662407 := by exact prefixLift 3662407
  have htrace : WordTrace (prefixWord ++ tailWord_3662407) baseStart_3662407 baseEnd_3662407 := by
    simpa [prefixWord, tailWord_3662407, baseEnd_3662407] using wordTrace_append hprefix tailTrace_3662407
  have hstable : (prefixWord ++ tailWord_3662407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662407).length < 2 ^ (prefixWord ++ tailWord_3662407).sum := by decide
  have hdescent : baseEnd_3662407 < baseStart_3662407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662417 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 1, 5]
def baseStart_3662417 : Nat := 118140960795 + 3662417 * 2 ^ 59
def prefixEnd_3662417 : Nat := 4983230072969 + 3 ^ 40 * 3662417 * 2
def baseEnd_3662417 : Nat := 626860092732567503448119

theorem tailTrace_3662417 : CollatzResearch.WordTrace tailWord_3662417 prefixEnd_3662417 626860092732567503448119 := by
  unfold tailWord_3662417
  simp only [CollatzResearch.WordTrace]
  refine ⟨133579321972696174870825505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89052881315130783247217003 133579321972696174870825505)
  ·
    refine ⟨100184491479522131153119129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133579321972696174870825505 100184491479522131153119129)
    ·
      refine ⟨75138368609641598364839347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100184491479522131153119129 75138368609641598364839347)
      ·
        refine ⟨112707552914462397547259021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75138368609641598364839347 112707552914462397547259021)
        ·
          refine ⟨42265332342923399080222133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112707552914462397547259021 42265332342923399080222133)
          ·
            refine ⟨3962374907149068663770825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42265332342923399080222133 3962374907149068663770825)
            ·
              refine ⟨2971781180361801497828119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3962374907149068663770825 2971781180361801497828119)
              ·
                refine ⟨4457671770542702246742179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971781180361801497828119 4457671770542702246742179)
                ·
                  refine ⟨6686507655814053370113269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457671770542702246742179 6686507655814053370113269)
                  ·
                    refine ⟨626860092732567503448119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6686507655814053370113269 626860092732567503448119)
                    ·
                      rfl

theorem cell23_3662417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_3662417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662417 prefixEnd_3662417 := by exact prefixLift 3662417
  have htrace : WordTrace (prefixWord ++ tailWord_3662417) baseStart_3662417 baseEnd_3662417 := by
    simpa [prefixWord, tailWord_3662417, baseEnd_3662417] using wordTrace_append hprefix tailTrace_3662417
  have hstable : (prefixWord ++ tailWord_3662417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662417).length < 2 ^ (prefixWord ++ tailWord_3662417).sum := by decide
  have hdescent : baseEnd_3662417 < baseStart_3662417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662423 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_3662423 : Nat := 118140960795 + 3662423 * 2 ^ 59
def prefixEnd_3662423 : Nat := 4983230072969 + 3 ^ 40 * 3662423 * 2
def baseEnd_3662423 : Nat := 1880583359081629486869329

theorem tailTrace_3662423 : CollatzResearch.WordTrace tailWord_3662423 prefixEnd_3662423 1880583359081629486869329 := by
  unfold tailWord_3662423
  simp only [CollatzResearch.WordTrace]
  refine ⟨133579540810674437895543923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89053027207116291930362615 133579540810674437895543923)
  ·
    refine ⟨200369311216011656843315885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133579540810674437895543923 200369311216011656843315885)
    ·
      refine ⟨75138491706004371316243457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200369311216011656843315885 75138491706004371316243457)
      ·
        refine ⟨56353868779503278487182593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75138491706004371316243457 56353868779503278487182593)
        ·
          refine ⟨42265401584627458865386945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56353868779503278487182593 42265401584627458865386945)
          ·
            refine ⟨31699051188470594149040209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42265401584627458865386945 31699051188470594149040209)
            ·
              refine ⟨23774288391352945611780157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31699051188470594149040209 23774288391352945611780157)
              ·
                refine ⟨8915358146757354604417559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23774288391352945611780157 8915358146757354604417559)
                ·
                  refine ⟨13373037220136031906626339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8915358146757354604417559 13373037220136031906626339)
                  ·
                    refine ⟨20059555830204047859939509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13373037220136031906626339 20059555830204047859939509)
                    ·
                      refine ⟨1880583359081629486869329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20059555830204047859939509 1880583359081629486869329)
                      ·
                        rfl

theorem cell23_3662423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_3662423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662423 prefixEnd_3662423 := by exact prefixLift 3662423
  have htrace : WordTrace (prefixWord ++ tailWord_3662423) baseStart_3662423 baseEnd_3662423 := by
    simpa [prefixWord, tailWord_3662423, baseEnd_3662423] using wordTrace_append hprefix tailTrace_3662423
  have hstable : (prefixWord ++ tailWord_3662423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662423).length < 2 ^ (prefixWord ++ tailWord_3662423).sum := by decide
  have hdescent : baseEnd_3662423 < baseStart_3662423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662450 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_3662450 : Nat := 118140960795 + 3662450 * 2 ^ 59
def prefixEnd_3662450 : Nat := 4983230072969 + 3 ^ 40 * 3662450 * 2
def baseEnd_3662450 : Nat := 1880597223059300881231705

theorem tailTrace_3662450 : CollatzResearch.WordTrace tailWord_3662450 prefixEnd_3662450 1880597223059300881231705 := by
  unfold tailWord_3662450
  simp only [CollatzResearch.WordTrace]
  refine ⟨33395131395394155376694201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89053683721051081004517869 33395131395394155376694201)
  ·
    refine ⟨25046348546545616532520651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33395131395394155376694201 25046348546545616532520651)
    ·
      refine ⟨37569522819818424798780977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25046348546545616532520651 37569522819818424798780977)
      ·
        refine ⟨28177142114863818599085733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37569522819818424798780977 28177142114863818599085733)
        ·
          refine ⟨5283214146536965987328575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28177142114863818599085733 5283214146536965987328575)
          ·
            refine ⟨7924821219805448980992863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283214146536965987328575 7924821219805448980992863)
            ·
              refine ⟨11887231829708173471489295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924821219805448980992863 11887231829708173471489295)
              ·
                refine ⟨17830847744562260207233943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11887231829708173471489295 17830847744562260207233943)
                ·
                  refine ⟨26746271616843390310850915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17830847744562260207233943 26746271616843390310850915)
                  ·
                    refine ⟨40119407425265085466276373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26746271616843390310850915 40119407425265085466276373)
                    ·
                      refine ⟨1880597223059300881231705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40119407425265085466276373 1880597223059300881231705)
                      ·
                        rfl

theorem cell23_3662450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_3662450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662450 prefixEnd_3662450 := by exact prefixLift 3662450
  have htrace : WordTrace (prefixWord ++ tailWord_3662450) baseStart_3662450 baseEnd_3662450 := by
    simpa [prefixWord, tailWord_3662450, baseEnd_3662450] using wordTrace_append hprefix tailTrace_3662450
  have hstable : (prefixWord ++ tailWord_3662450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662450).length < 2 ^ (prefixWord ++ tailWord_3662450).sum := by decide
  have hdescent : baseEnd_3662450 < baseStart_3662450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662454 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3662454 : Nat := 118140960795 + 3662454 * 2 ^ 59
def prefixEnd_3662454 : Nat := 4983230072969 + 3 ^ 40 * 3662454 * 2
def baseEnd_3662454 : Nat := 1880599276981918865581687

theorem tailTrace_3662454 : CollatzResearch.WordTrace tailWord_3662454 prefixEnd_3662454 1880599276981918865581687 := by
  unfold tailWord_3662454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8348791967097633136870151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89053780982374753459948277 8348791967097633136870151)
  ·
    refine ⟨12523187950646449705305227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8348791967097633136870151 12523187950646449705305227)
    ·
      refine ⟨18784781925969674557957841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12523187950646449705305227 18784781925969674557957841)
      ·
        refine ⟨14088586444477255918468381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18784781925969674557957841 14088586444477255918468381)
        ·
          refine ⟨5283219916678970969425643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14088586444477255918468381 5283219916678970969425643)
          ·
            refine ⟨7924829875018456454138465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283219916678970969425643 7924829875018456454138465)
            ·
              refine ⟨5943622406263842340603849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7924829875018456454138465 5943622406263842340603849)
              ·
                refine ⟨4457716804697881755452887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5943622406263842340603849 4457716804697881755452887)
                ·
                  refine ⟨6686575207046822633179331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457716804697881755452887 6686575207046822633179331)
                  ·
                    refine ⟨10029862810570233949768997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6686575207046822633179331 10029862810570233949768997)
                    ·
                      refine ⟨1880599276981918865581687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10029862810570233949768997 1880599276981918865581687)
                      ·
                        rfl

theorem cell23_3662454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3662454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662454 prefixEnd_3662454 := by exact prefixLift 3662454
  have htrace : WordTrace (prefixWord ++ tailWord_3662454) baseStart_3662454 baseEnd_3662454 := by
    simpa [prefixWord, tailWord_3662454, baseEnd_3662454] using wordTrace_append hprefix tailTrace_3662454
  have hstable : (prefixWord ++ tailWord_3662454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662454).length < 2 ^ (prefixWord ++ tailWord_3662454).sum := by decide
  have hdescent : baseEnd_3662454 < baseStart_3662454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662457 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 3]
def baseStart_3662457 : Nat := 118140960795 + 3662457 * 2 ^ 59
def prefixEnd_3662457 : Nat := 4983230072969 + 3 ^ 40 * 3662457 * 2
def baseEnd_3662457 : Nat := 1880600817423882353844173

theorem tailTrace_3662457 : CollatzResearch.WordTrace tailWord_3662457 prefixEnd_3662457 1880600817423882353844173 := by
  unfold tailWord_3662457
  simp only [CollatzResearch.WordTrace]
  refine ⟨133580780892551261702281625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89053853928367507801521083 133580780892551261702281625)
  ·
    refine ⟨100185585669413446276711219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133580780892551261702281625 100185585669413446276711219)
    ·
      refine ⟨150278378504120169415066829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100185585669413446276711219 150278378504120169415066829)
      ·
        refine ⟨56354391939045063530650061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150278378504120169415066829 56354391939045063530650061)
        ·
          refine ⟨21132896977141898823993773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56354391939045063530650061 21132896977141898823993773)
          ·
            refine ⟨7924836366428212058997665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21132896977141898823993773 7924836366428212058997665)
            ·
              refine ⟨5943627274821159044248249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7924836366428212058997665 5943627274821159044248249)
              ·
                refine ⟨4457720456115869283186187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5943627274821159044248249 4457720456115869283186187)
                ·
                  refine ⟨6686580684173803924779281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457720456115869283186187 6686580684173803924779281)
                  ·
                    refine ⟨5014935513130352943584461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6686580684173803924779281 5014935513130352943584461)
                    ·
                      refine ⟨1880600817423882353844173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5014935513130352943584461 1880600817423882353844173)
                      ·
                        rfl

theorem cell23_3662457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_3662457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662457 prefixEnd_3662457 := by exact prefixLift 3662457
  have htrace : WordTrace (prefixWord ++ tailWord_3662457) baseStart_3662457 baseEnd_3662457 := by
    simpa [prefixWord, tailWord_3662457, baseEnd_3662457] using wordTrace_append hprefix tailTrace_3662457
  have hstable : (prefixWord ++ tailWord_3662457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662457).length < 2 ^ (prefixWord ++ tailWord_3662457).sum := by decide
  have hdescent : baseEnd_3662457 < baseStart_3662457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662480 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 7, 3, 2]
def baseStart_3662480 : Nat := 118140960795 + 3662480 * 2 ^ 59
def prefixEnd_3662480 : Nat := 4983230072969 + 3 ^ 40 * 3662480 * 2
def baseEnd_3662480 : Nat := 1880612627478935763856567

theorem tailTrace_3662480 : CollatzResearch.WordTrace tailWord_3662480 prefixEnd_3662480 1880612627478935763856567 := by
  unfold tailWord_3662480
  simp only [CollatzResearch.WordTrace]
  refine ⟨66790809885733968315184447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89054413180978624420245929 66790809885733968315184447)
  ·
    refine ⟨100186214828600952472776671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66790809885733968315184447 100186214828600952472776671)
    ·
      refine ⟨150279322242901428709165007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100186214828600952472776671 150279322242901428709165007)
      ·
        refine ⟨225418983364352143063747511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150279322242901428709165007 225418983364352143063747511)
        ·
          refine ⟨338128475046528214595621267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225418983364352143063747511 338128475046528214595621267)
          ·
            refine ⟨507192712569792321893431901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338128475046528214595621267 507192712569792321893431901)
            ·
              refine ⟨190197267213672120710036963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507192712569792321893431901 190197267213672120710036963)
              ·
                refine ⟨285295900820508181065055445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190197267213672120710036963 285295900820508181065055445)
                ·
                  refine ⟨6686622675480660493712237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 285295900820508181065055445 6686622675480660493712237)
                  ·
                    refine ⟨2507483503305247685142089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6686622675480660493712237 2507483503305247685142089)
                    ·
                      refine ⟨1880612627478935763856567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507483503305247685142089 1880612627478935763856567)
                      ·
                        rfl

theorem cell23_3662480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 3, 2].length) (baseStart_3662480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662480 prefixEnd_3662480 := by exact prefixLift 3662480
  have htrace : WordTrace (prefixWord ++ tailWord_3662480) baseStart_3662480 baseEnd_3662480 := by
    simpa [prefixWord, tailWord_3662480, baseEnd_3662480] using wordTrace_append hprefix tailTrace_3662480
  have hstable : (prefixWord ++ tailWord_3662480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662480).length < 2 ^ (prefixWord ++ tailWord_3662480).sum := by decide
  have hdescent : baseEnd_3662480 < baseStart_3662480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662487 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 3]
def baseStart_3662487 : Nat := 118140960795 + 3662487 * 2 ^ 59
def prefixEnd_3662487 : Nat := 4983230072969 + 3 ^ 40 * 3662487 * 2
def baseEnd_3662487 : Nat := 1880616221843517236469035

theorem tailTrace_3662487 : CollatzResearch.WordTrace tailWord_3662487 prefixEnd_3662487 1880616221843517236469035 := by
  unfold tailWord_3662487
  simp only [CollatzResearch.WordTrace]
  refine ⟨133581875082442576825873715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89054583388295051217249143 133581875082442576825873715)
  ·
    refine ⟨200372812623663865238810573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133581875082442576825873715 200372812623663865238810573)
    ·
      refine ⟨75139804733873949464553965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200372812623663865238810573 75139804733873949464553965)
      ·
        refine ⟨28177426775202731049207737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75139804733873949464553965 28177426775202731049207737)
        ·
          refine ⟨21133070081402048286905803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28177426775202731049207737 21133070081402048286905803)
          ·
            refine ⟨31699605122103072430358705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21133070081402048286905803 31699605122103072430358705)
            ·
              refine ⟨23774703841577304322769029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31699605122103072430358705 23774703841577304322769029)
              ·
                refine ⟨4457756970295744560519193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23774703841577304322769029 4457756970295744560519193)
                ·
                  refine ⟨3343317727721808420389395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457756970295744560519193 3343317727721808420389395)
                  ·
                    refine ⟨5014976591582712630584093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3343317727721808420389395 5014976591582712630584093)
                    ·
                      refine ⟨1880616221843517236469035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5014976591582712630584093 1880616221843517236469035)
                      ·
                        rfl

theorem cell23_3662487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_3662487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662487 prefixEnd_3662487 := by exact prefixLift 3662487
  have htrace : WordTrace (prefixWord ++ tailWord_3662487) baseStart_3662487 baseEnd_3662487 := by
    simpa [prefixWord, tailWord_3662487, baseEnd_3662487] using wordTrace_append hprefix tailTrace_3662487
  have hstable : (prefixWord ++ tailWord_3662487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662487).length < 2 ^ (prefixWord ++ tailWord_3662487).sum := by decide
  have hdescent : baseEnd_3662487 < baseStart_3662487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662523 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 4]
def baseStart_3662523 : Nat := 118140960795 + 3662523 * 2 ^ 59
def prefixEnd_3662523 : Nat := 4983230072969 + 3 ^ 40 * 3662523 * 2
def baseEnd_3662523 : Nat := 1880634707147079095618869

theorem tailTrace_3662523 : CollatzResearch.WordTrace tailWord_3662523 prefixEnd_3662523 1880634707147079095618869 := by
  unfold tailWord_3662523
  simp only [CollatzResearch.WordTrace]
  refine ⟨133583188110312154974184223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89055458740208103316122815 133583188110312154974184223)
  ·
    refine ⟨200374782165468232461276335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133583188110312154974184223 200374782165468232461276335)
    ·
      refine ⟨300562173248202348691914503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200374782165468232461276335 300562173248202348691914503)
      ·
        refine ⟨450843259872303523037871755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300562173248202348691914503 450843259872303523037871755)
        ·
          refine ⟨676264889808455284556807633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450843259872303523037871755 676264889808455284556807633)
          ·
            refine ⟨507198667356341463417605725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676264889808455284556807633 507198667356341463417605725)
            ·
              refine ⟨190199500258628048781602147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507198667356341463417605725 190199500258628048781602147)
              ·
                refine ⟨285299250387942073172403221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190199500258628048781602147 285299250387942073172403221)
                ·
                  refine ⟨13373402361934784679956401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 285299250387942073172403221 13373402361934784679956401)
                  ·
                    refine ⟨10030051771451088509967301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13373402361934784679956401 10030051771451088509967301)
                    ·
                      refine ⟨1880634707147079095618869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10030051771451088509967301 1880634707147079095618869)
                      ·
                        rfl

theorem cell23_3662523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 4].length) (baseStart_3662523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662523 prefixEnd_3662523 := by exact prefixLift 3662523
  have htrace : WordTrace (prefixWord ++ tailWord_3662523) baseStart_3662523 baseEnd_3662523 := by
    simpa [prefixWord, tailWord_3662523, baseEnd_3662523] using wordTrace_append hprefix tailTrace_3662523
  have hstable : (prefixWord ++ tailWord_3662523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662523).length < 2 ^ (prefixWord ++ tailWord_3662523).sum := by decide
  have hdescent : baseEnd_3662523 < baseStart_3662523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662527 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 1, 4, 2]
def baseStart_3662527 : Nat := 118140960795 + 3662527 * 2 ^ 59
def prefixEnd_3662527 : Nat := 4983230072969 + 3 ^ 40 * 3662527 * 2
def baseEnd_3662527 : Nat := 1880636761069697079968851

theorem tailTrace_3662527 : CollatzResearch.WordTrace tailWord_3662527 prefixEnd_3662527 1880636761069697079968851 := by
  unfold tailWord_3662527
  simp only [CollatzResearch.WordTrace]
  refine ⟨133583334002297663657329835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89055556001531775771553223 133583334002297663657329835)
  ·
    refine ⟨200375001003446495485994753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133583334002297663657329835 200375001003446495485994753)
    ·
      refine ⟨150281250752584871614496065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200375001003446495485994753 150281250752584871614496065)
      ·
        refine ⟨112710938064438653710872049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150281250752584871614496065 112710938064438653710872049)
        ·
          refine ⟨84533203548328990283154037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112710938064438653710872049 84533203548328990283154037)
          ·
            refine ⟨7924987832655842839045691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84533203548328990283154037 7924987832655842839045691)
            ·
              refine ⟨11887481748983764258568537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924987832655842839045691 11887481748983764258568537)
              ·
                refine ⟨8915611311737823193926403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887481748983764258568537 8915611311737823193926403)
                ·
                  refine ⟨13373416967606734790889605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8915611311737823193926403 13373416967606734790889605)
                  ·
                    refine ⟨2507515681426262773291801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13373416967606734790889605 2507515681426262773291801)
                    ·
                      refine ⟨1880636761069697079968851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507515681426262773291801 1880636761069697079968851)
                      ·
                        rfl

theorem cell23_3662527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_3662527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662527 prefixEnd_3662527 := by exact prefixLift 3662527
  have htrace : WordTrace (prefixWord ++ tailWord_3662527) baseStart_3662527 baseEnd_3662527 := by
    simpa [prefixWord, tailWord_3662527, baseEnd_3662527] using wordTrace_append hprefix tailTrace_3662527
  have hstable : (prefixWord ++ tailWord_3662527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662527).length < 2 ^ (prefixWord ++ tailWord_3662527).sum := by decide
  have hdescent : baseEnd_3662527 < baseStart_3662527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662701 : List Nat := [1, 5, 1, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_3662701 : Nat := 118140960795 + 3662701 * 2 ^ 59
def prefixEnd_3662701 : Nat := 4983230072969 + 3 ^ 40 * 3662701 * 2
def baseEnd_3662701 : Nat := 1880726106703579399193051

theorem tailTrace_3662701 : CollatzResearch.WordTrace tailWord_3662701 prefixEnd_3662701 1880726106703579399193051 := by
  unfold tailWord_3662701
  simp only [CollatzResearch.WordTrace]
  refine ⟨133589680303667291374163957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89059786869111527582775971 133589680303667291374163957)
  ·
    refine ⟨12524032528468808566327871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133589680303667291374163957 12524032528468808566327871)
    ·
      refine ⟨18786048792703212849491807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12524032528468808566327871 18786048792703212849491807)
      ·
        refine ⟨28179073189054819274237711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18786048792703212849491807 28179073189054819274237711)
        ·
          refine ⟨42268609783582228911356567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28179073189054819274237711 42268609783582228911356567)
          ·
            refine ⟨63402914675373343367034851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42268609783582228911356567 63402914675373343367034851)
            ·
              refine ⟨95104372013060015050552277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63402914675373343367034851 95104372013060015050552277)
              ·
                refine ⟨2229008719056094102747319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95104372013060015050552277 2229008719056094102747319)
                ·
                  refine ⟨3343513078584141154120979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229008719056094102747319 3343513078584141154120979)
                  ·
                    refine ⟨5015269617876211731181469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3343513078584141154120979 5015269617876211731181469)
                    ·
                      refine ⟨1880726106703579399193051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5015269617876211731181469 1880726106703579399193051)
                      ·
                        rfl

theorem cell23_3662701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_3662701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662701 prefixEnd_3662701 := by exact prefixLift 3662701
  have htrace : WordTrace (prefixWord ++ tailWord_3662701) baseStart_3662701 baseEnd_3662701 := by
    simpa [prefixWord, tailWord_3662701, baseEnd_3662701] using wordTrace_append hprefix tailTrace_3662701
  have hstable : (prefixWord ++ tailWord_3662701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662701).length < 2 ^ (prefixWord ++ tailWord_3662701).sum := by decide
  have hdescent : baseEnd_3662701 < baseStart_3662701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662707 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 4]
def baseStart_3662707 : Nat := 118140960795 + 3662707 * 2 ^ 59
def prefixEnd_3662707 : Nat := 4983230072969 + 3 ^ 40 * 3662707 * 2
def baseEnd_3662707 : Nat := 1880729187587506375718023

theorem tailTrace_3662707 : CollatzResearch.WordTrace tailWord_3662707 prefixEnd_3662707 1880729187587506375718023 := by
  unfold tailWord_3662707
  simp only [CollatzResearch.WordTrace]
  refine ⟨133589899141645554398882375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89059932761097036265921583 133589899141645554398882375)
  ·
    refine ⟨200384848712468331598323563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133589899141645554398882375 200384848712468331598323563)
    ·
      refine ⟨300577273068702497397485345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200384848712468331598323563 300577273068702497397485345)
      ·
        refine ⟨225432954801526873048114009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300577273068702497397485345 225432954801526873048114009)
        ·
          refine ⟨169074716101145154786085507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225432954801526873048114009 169074716101145154786085507)
          ·
            refine ⟨253612074151717732179128261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169074716101145154786085507 253612074151717732179128261)
            ·
              refine ⟨47552263903447074783586549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253612074151717732179128261 47552263903447074783586549)
              ·
                refine ⟨4458024740948163260961239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47552263903447074783586549 4458024740948163260961239)
                ·
                  refine ⟨6687037111422244891441859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4458024740948163260961239 6687037111422244891441859)
                  ·
                    refine ⟨10030555667133367337162789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6687037111422244891441859 10030555667133367337162789)
                    ·
                      refine ⟨1880729187587506375718023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10030555667133367337162789 1880729187587506375718023)
                      ·
                        rfl

theorem cell23_3662707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 4].length) (baseStart_3662707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662707 prefixEnd_3662707 := by exact prefixLift 3662707
  have htrace : WordTrace (prefixWord ++ tailWord_3662707) baseStart_3662707 baseEnd_3662707 := by
    simpa [prefixWord, tailWord_3662707, baseEnd_3662707] using wordTrace_append hprefix tailTrace_3662707
  have hstable : (prefixWord ++ tailWord_3662707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662707).length < 2 ^ (prefixWord ++ tailWord_3662707).sum := by decide
  have hdescent : baseEnd_3662707 < baseStart_3662707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662717 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_3662717 : Nat := 118140960795 + 3662717 * 2 ^ 59
def prefixEnd_3662717 : Nat := 4983230072969 + 3 ^ 40 * 3662717 * 2
def baseEnd_3662717 : Nat := 626911440798017112197659

theorem tailTrace_3662717 : CollatzResearch.WordTrace tailWord_3662717 prefixEnd_3662717 626911440798017112197659 := by
  unfold tailWord_3662717
  simp only [CollatzResearch.WordTrace]
  refine ⟨133590263871609326106746405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89060175914406217404497603 133590263871609326106746405)
  ·
    refine ⟨25048174475926748645014951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133590263871609326106746405 25048174475926748645014951)
    ·
      refine ⟨37572261713890122967522427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25048174475926748645014951 37572261713890122967522427)
      ·
        refine ⟨56358392570835184451283641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37572261713890122967522427 56358392570835184451283641)
        ·
          refine ⟨42268794428126388338462731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56358392570835184451283641 42268794428126388338462731)
          ·
            refine ⟨63403191642189582507694097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42268794428126388338462731 63403191642189582507694097)
            ·
              refine ⟨47552393731642186880770573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63403191642189582507694097 47552393731642186880770573)
              ·
                refine ⟨17832147649365820080288965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47552393731642186880770573 17832147649365820080288965)
                ·
                  refine ⟨3343527684256091265054181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17832147649365820080288965 3343527684256091265054181)
                  ·
                    refine ⟨626911440798017112197659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3343527684256091265054181 626911440798017112197659)
                    ·
                      rfl

theorem cell23_3662717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_3662717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662717 prefixEnd_3662717 := by exact prefixLift 3662717
  have htrace : WordTrace (prefixWord ++ tailWord_3662717) baseStart_3662717 baseEnd_3662717 := by
    simpa [prefixWord, tailWord_3662717, baseEnd_3662717] using wordTrace_append hprefix tailTrace_3662717
  have hstable : (prefixWord ++ tailWord_3662717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662717).length < 2 ^ (prefixWord ++ tailWord_3662717).sum := by decide
  have hdescent : baseEnd_3662717 < baseStart_3662717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662720 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_3662720 : Nat := 118140960795 + 3662720 * 2 ^ 59
def prefixEnd_3662720 : Nat := 4983230072969 + 3 ^ 40 * 3662720 * 2
def baseEnd_3662720 : Nat := 1880735862836014824855463

theorem tailTrace_3662720 : CollatzResearch.WordTrace tailWord_3662720 prefixEnd_3662720 1880735862836014824855463 := by
  unfold tailWord_3662720
  simp only [CollatzResearch.WordTrace]
  refine ⟨66795186645299228809552807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89060248860398971746070409 66795186645299228809552807)
  ·
    refine ⟨100192779967948843214329211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66795186645299228809552807 100192779967948843214329211)
    ·
      refine ⟨150289169951923264821493817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100192779967948843214329211 150289169951923264821493817)
      ·
        refine ⟨112716877463942448616120363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150289169951923264821493817 112716877463942448616120363)
        ·
          refine ⟨169075316195913672924180545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112716877463942448616120363 169075316195913672924180545)
          ·
            refine ⟨126806487146935254693135409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169075316195913672924180545 126806487146935254693135409)
            ·
              refine ⟨95104865360201441019851557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126806487146935254693135409 95104865360201441019851557)
              ·
                refine ⟨17832162255037770191222167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95104865360201441019851557 17832162255037770191222167)
                ·
                  refine ⟨26748243382556655286833251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17832162255037770191222167 26748243382556655286833251)
                  ·
                    refine ⟨40122365073834982930249877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26748243382556655286833251 40122365073834982930249877)
                    ·
                      refine ⟨1880735862836014824855463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40122365073834982930249877 1880735862836014824855463)
                      ·
                        rfl

theorem cell23_3662720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_3662720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662720 prefixEnd_3662720 := by exact prefixLift 3662720
  have htrace : WordTrace (prefixWord ++ tailWord_3662720) baseStart_3662720 baseEnd_3662720 := by
    simpa [prefixWord, tailWord_3662720, baseEnd_3662720] using wordTrace_append hprefix tailTrace_3662720
  have hstable : (prefixWord ++ tailWord_3662720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662720).length < 2 ^ (prefixWord ++ tailWord_3662720).sum := by decide
  have hdescent : baseEnd_3662720 < baseStart_3662720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662741 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_3662741 : Nat := 118140960795 + 3662741 * 2 ^ 59
def prefixEnd_3662741 : Nat := 4983230072969 + 3 ^ 40 * 3662741 * 2
def baseEnd_3662741 : Nat := 1880746645929759242692867

theorem tailTrace_3662741 : CollatzResearch.WordTrace tailWord_3662741 prefixEnd_3662741 1880746645929759242692867 := by
  unfold tailWord_3662741
  simp only [CollatzResearch.WordTrace]
  refine ⟨133591139223522378205620077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89060759482348252137080051 133591139223522378205620077)
  ·
    refine ⟨50096677208820891827107529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133591139223522378205620077 50096677208820891827107529)
    ·
      refine ⟨37572507906615668870330647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50096677208820891827107529 37572507906615668870330647)
      ·
        refine ⟨56358761859923503305495971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37572507906615668870330647 56358761859923503305495971)
        ·
          refine ⟨84538142789885254958243957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56358761859923503305495971 84538142789885254958243957)
          ·
            refine ⟨7925450886551742652335371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84538142789885254958243957 7925450886551742652335371)
            ·
              refine ⟨11888176329827613978503057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7925450886551742652335371 11888176329827613978503057)
              ·
                refine ⟨8916132247370710483877293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11888176329827613978503057 8916132247370710483877293)
                ·
                  refine ⟨3343549592764016431453985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8916132247370710483877293 3343549592764016431453985)
                  ·
                    refine ⟨2507662194573012323590489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3343549592764016431453985 2507662194573012323590489)
                    ·
                      refine ⟨1880746645929759242692867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507662194573012323590489 1880746645929759242692867)
                      ·
                        rfl

theorem cell23_3662741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_3662741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662741 prefixEnd_3662741 := by exact prefixLift 3662741
  have htrace : WordTrace (prefixWord ++ tailWord_3662741) baseStart_3662741 baseEnd_3662741 := by
    simpa [prefixWord, tailWord_3662741, baseEnd_3662741] using wordTrace_append hprefix tailTrace_3662741
  have hstable : (prefixWord ++ tailWord_3662741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662741).length < 2 ^ (prefixWord ++ tailWord_3662741).sum := by decide
  have hdescent : baseEnd_3662741 < baseStart_3662741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662754 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3662754 : Nat := 118140960795 + 3662754 * 2 ^ 59
def prefixEnd_3662754 : Nat := 4983230072969 + 3 ^ 40 * 3662754 * 2
def baseEnd_3662754 : Nat := 1880753321178267691830307

theorem tailTrace_3662754 : CollatzResearch.WordTrace tailWord_3662754 prefixEnd_3662754 1880753321178267691830307 := by
  unfold tailWord_3662754
  simp only [CollatzResearch.WordTrace]
  refine ⟨33397903343118820356460829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89061075581650187617228877 33397903343118820356460829)
  ·
    refine ⟨12524213753669557633672811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33397903343118820356460829 12524213753669557633672811)
    ·
      refine ⟨18786320630504336450509217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12524213753669557633672811 18786320630504336450509217)
      ·
        refine ⟨14089740472878252337881913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18786320630504336450509217 14089740472878252337881913)
        ·
          refine ⟨10567305354658689253411435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14089740472878252337881913 10567305354658689253411435)
          ·
            refine ⟨15850958031988033880117153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10567305354658689253411435 15850958031988033880117153)
            ·
              refine ⟨11888218523991025410087865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15850958031988033880117153 11888218523991025410087865)
              ·
                refine ⟨8916163892993269057565899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11888218523991025410087865 8916163892993269057565899)
                ·
                  refine ⟨13374245839489903586348849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8916163892993269057565899 13374245839489903586348849)
                  ·
                    refine ⟨10030684379617427689761637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13374245839489903586348849 10030684379617427689761637)
                    ·
                      refine ⟨1880753321178267691830307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10030684379617427689761637 1880753321178267691830307)
                      ·
                        rfl

theorem cell23_3662754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3662754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662754 prefixEnd_3662754 := by exact prefixLift 3662754
  have htrace : WordTrace (prefixWord ++ tailWord_3662754) baseStart_3662754 baseEnd_3662754 := by
    simpa [prefixWord, tailWord_3662754, baseEnd_3662754] using wordTrace_append hprefix tailTrace_3662754
  have hstable : (prefixWord ++ tailWord_3662754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662754).length < 2 ^ (prefixWord ++ tailWord_3662754).sum := by decide
  have hdescent : baseEnd_3662754 < baseStart_3662754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662788 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3662788 : Nat := 118140960795 + 3662788 * 2 ^ 59
def prefixEnd_3662788 : Nat := 4983230072969 + 3 ^ 40 * 3662788 * 2
def baseEnd_3662788 : Nat := 1880770779520520558805151

theorem tailTrace_3662788 : CollatzResearch.WordTrace tailWord_3662788 prefixEnd_3662788 1880770779520520558805151 := by
  unfold tailWord_3662788
  simp only [CollatzResearch.WordTrace]
  refine ⟨66796426727176052616290509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89061902302901403488387345 66796426727176052616290509)
  ·
    refine ⟨25048660022691019731108941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66796426727176052616290509 25048660022691019731108941)
    ·
      refine ⟨9393247508509132399165853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25048660022691019731108941 9393247508509132399165853)
      ·
        refine ⟨3522467815690924649687195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9393247508509132399165853 3522467815690924649687195)
        ·
          refine ⟨5283701723536386974530793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522467815690924649687195 5283701723536386974530793)
          ·
            refine ⟨3962776292652290230898095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5283701723536386974530793 3962776292652290230898095)
            ·
              refine ⟨5944164438978435346347143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3962776292652290230898095 5944164438978435346347143)
              ·
                refine ⟨8916246658467653019520715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5944164438978435346347143 8916246658467653019520715)
                ·
                  refine ⟨13374369987701479529281073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8916246658467653019520715 13374369987701479529281073)
                  ·
                    refine ⟨10030777490776109646960805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13374369987701479529281073 10030777490776109646960805)
                    ·
                      refine ⟨1880770779520520558805151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10030777490776109646960805 1880770779520520558805151)
                      ·
                        rfl

theorem cell23_3662788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3662788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662788 prefixEnd_3662788 := by exact prefixLift 3662788
  have htrace : WordTrace (prefixWord ++ tailWord_3662788) baseStart_3662788 baseEnd_3662788 := by
    simpa [prefixWord, tailWord_3662788, baseEnd_3662788] using wordTrace_append hprefix tailTrace_3662788
  have hstable : (prefixWord ++ tailWord_3662788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662788).length < 2 ^ (prefixWord ++ tailWord_3662788).sum := by decide
  have hdescent : baseEnd_3662788 < baseStart_3662788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662801 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 1, 3, 2]
def baseStart_3662801 : Nat := 118140960795 + 3662801 * 2 ^ 59
def prefixEnd_3662801 : Nat := 4983230072969 + 3 ^ 40 * 3662801 * 2
def baseEnd_3662801 : Nat := 1880777454769029007942591

theorem tailTrace_3662801 : CollatzResearch.WordTrace tailWord_3662801 prefixEnd_3662801 1880777454769029007942591 := by
  unfold tailWord_3662801
  simp only [CollatzResearch.WordTrace]
  refine ⟨133593327603305008452804257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89062218402203338968536171 133593327603305008452804257)
  ·
    refine ⟨100194995702478756339603193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133593327603305008452804257 100194995702478756339603193)
    ·
      refine ⟨75146246776859067254702395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100194995702478756339603193 75146246776859067254702395)
      ·
        refine ⟨112719370165288600882053593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75146246776859067254702395 112719370165288600882053593)
        ·
          refine ⟨84539527623966450661540195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112719370165288600882053593 84539527623966450661540195)
          ·
            refine ⟨126809291435949675992310293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84539527623966450661540195 126809291435949675992310293)
            ·
              refine ⟨5944185536060141062139545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126809291435949675992310293 5944185536060141062139545)
              ·
                refine ⟨4458139152045105796604659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5944185536060141062139545 4458139152045105796604659)
                ·
                  refine ⟨6687208728067658694906989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4458139152045105796604659 6687208728067658694906989)
                  ·
                    refine ⟨2507703273025372010590121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6687208728067658694906989 2507703273025372010590121)
                    ·
                      refine ⟨1880777454769029007942591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507703273025372010590121 1880777454769029007942591)
                      ·
                        rfl

theorem cell23_3662801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_3662801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662801 prefixEnd_3662801 := by exact prefixLift 3662801
  have htrace : WordTrace (prefixWord ++ tailWord_3662801) baseStart_3662801 baseEnd_3662801 := by
    simpa [prefixWord, tailWord_3662801, baseEnd_3662801] using wordTrace_append hprefix tailTrace_3662801
  have hstable : (prefixWord ++ tailWord_3662801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662801).length < 2 ^ (prefixWord ++ tailWord_3662801).sum := by decide
  have hdescent : baseEnd_3662801 < baseStart_3662801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662817 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_3662817 : Nat := 118140960795 + 3662817 * 2 ^ 59
def prefixEnd_3662817 : Nat := 4983230072969 + 3 ^ 40 * 3662817 * 2
def baseEnd_3662817 : Nat := 1880785670459500945342517

theorem tailTrace_3662817 : CollatzResearch.WordTrace tailWord_3662817 prefixEnd_3662817 1880785670459500945342517 := by
  unfold tailWord_3662817
  simp only [CollatzResearch.WordTrace]
  refine ⟨133593911171247043185386705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89062607447498028790257803 133593911171247043185386705)
  ·
    refine ⟨100195433378435282389040029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133593911171247043185386705 100195433378435282389040029)
    ·
      refine ⟨37573287516913230895890011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100195433378435282389040029 37573287516913230895890011)
      ·
        refine ⟨56359931275369846343835017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37573287516913230895890011 56359931275369846343835017)
        ·
          refine ⟨42269948456527384757876263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56359931275369846343835017 42269948456527384757876263)
          ·
            refine ⟨63404922684791077136814395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42269948456527384757876263 63404922684791077136814395)
            ·
              refine ⟨95107384027186615705221593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63404922684791077136814395 95107384027186615705221593)
              ·
                refine ⟨71330538020389961778916195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95107384027186615705221593 71330538020389961778916195)
                ·
                  refine ⟨106995807030584942668374293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71330538020389961778916195 106995807030584942668374293)
                  ·
                    refine ⟨5015428454558669187580045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106995807030584942668374293 5015428454558669187580045)
                    ·
                      refine ⟨1880785670459500945342517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5015428454558669187580045 1880785670459500945342517)
                      ·
                        rfl

theorem cell23_3662817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_3662817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662817 prefixEnd_3662817 := by exact prefixLift 3662817
  have htrace : WordTrace (prefixWord ++ tailWord_3662817) baseStart_3662817 baseEnd_3662817 := by
    simpa [prefixWord, tailWord_3662817, baseEnd_3662817] using wordTrace_append hprefix tailTrace_3662817
  have hstable : (prefixWord ++ tailWord_3662817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662817).length < 2 ^ (prefixWord ++ tailWord_3662817).sum := by decide
  have hdescent : baseEnd_3662817 < baseStart_3662817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662831 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 4, 2, 2]
def baseStart_3662831 : Nat := 118140960795 + 3662831 * 2 ^ 59
def prefixEnd_3662831 : Nat := 4983230072969 + 3 ^ 40 * 3662831 * 2
def baseEnd_3662831 : Nat := 1880792859188663890567453

theorem tailTrace_3662831 : CollatzResearch.WordTrace tailWord_3662831 prefixEnd_3662831 1880792859188663890567453 := by
  unfold tailWord_3662831
  simp only [CollatzResearch.WordTrace]
  refine ⟨133594421793196323576396347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89062947862130882384264231 133594421793196323576396347)
  ·
    refine ⟨200391632689794485364594521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133594421793196323576396347 200391632689794485364594521)
    ·
      refine ⟨150293724517345864023445891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200391632689794485364594521 150293724517345864023445891)
      ·
        refine ⟨225440586776018796035168837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150293724517345864023445891 225440586776018796035168837)
        ·
          refine ⟨42270110020503524256594157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225440586776018796035168837 42270110020503524256594157)
          ·
            refine ⟨15851291257688821596222809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42270110020503524256594157 15851291257688821596222809)
            ·
              refine ⟨11888468443266616197167107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15851291257688821596222809 11888468443266616197167107)
              ·
                refine ⟨17832702664899924295750661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11888468443266616197167107 17832702664899924295750661)
                ·
                  refine ⟨3343631749668735805453249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17832702664899924295750661 3343631749668735805453249)
                  ·
                    refine ⟨2507723812251551854089937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3343631749668735805453249 2507723812251551854089937)
                    ·
                      refine ⟨1880792859188663890567453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507723812251551854089937 1880792859188663890567453)
                      ·
                        rfl

theorem cell23_3662831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 2, 2].length) (baseStart_3662831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662831 prefixEnd_3662831 := by exact prefixLift 3662831
  have htrace : WordTrace (prefixWord ++ tailWord_3662831) baseStart_3662831 baseEnd_3662831 := by
    simpa [prefixWord, tailWord_3662831, baseEnd_3662831] using wordTrace_append hprefix tailTrace_3662831
  have hstable : (prefixWord ++ tailWord_3662831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662831).length < 2 ^ (prefixWord ++ tailWord_3662831).sum := by decide
  have hdescent : baseEnd_3662831 < baseStart_3662831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662836 : List Nat := [2, 6, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3662836 : Nat := 118140960795 + 3662836 * 2 ^ 59
def prefixEnd_3662836 : Nat := 4983230072969 + 3 ^ 40 * 3662836 * 2
def baseEnd_3662836 : Nat := 626931808863978790334977

theorem tailTrace_3662836 : CollatzResearch.WordTrace tailWord_3662836 prefixEnd_3662836 626931808863978790334977 := by
  unfold tailWord_3662836
  simp only [CollatzResearch.WordTrace]
  refine ⟨66797302079089104715164181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89063069438785472953552241 66797302079089104715164181)
  ·
    refine ⟨3131123534957301783523321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66797302079089104715164181 3131123534957301783523321)
    ·
      refine ⟨2348342651217976337642491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3131123534957301783523321 2348342651217976337642491)
      ·
        refine ⟨3522513976826964506463737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348342651217976337642491 3522513976826964506463737)
        ·
          refine ⟨2641885482620223379847803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3522513976826964506463737 2641885482620223379847803)
          ·
            refine ⟨3962828223930335069771705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2641885482620223379847803 3962828223930335069771705)
            ·
              refine ⟨2972121167947751302328779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3962828223930335069771705 2972121167947751302328779)
              ·
                refine ⟨4458181751921626953493169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2972121167947751302328779 4458181751921626953493169)
                ·
                  refine ⟨3343636313941220215119877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4458181751921626953493169 3343636313941220215119877)
                  ·
                    refine ⟨626931808863978790334977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3343636313941220215119877 626931808863978790334977)
                    ·
                      rfl

theorem cell23_3662836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3662836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662836 prefixEnd_3662836 := by exact prefixLift 3662836
  have htrace : WordTrace (prefixWord ++ tailWord_3662836) baseStart_3662836 baseEnd_3662836 := by
    simpa [prefixWord, tailWord_3662836, baseEnd_3662836] using wordTrace_append hprefix tailTrace_3662836
  have hstable : (prefixWord ++ tailWord_3662836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662836).length < 2 ^ (prefixWord ++ tailWord_3662836).sum := by decide
  have hdescent : baseEnd_3662836 < baseStart_3662836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662894 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3662894 : Nat := 118140960795 + 3662894 * 2 ^ 59
def prefixEnd_3662894 : Nat := 4983230072969 + 3 ^ 40 * 3662894 * 2
def baseEnd_3662894 : Nat := 1880825208469897144079663

theorem tailTrace_3662894 : CollatzResearch.WordTrace tailWord_3662894 prefixEnd_3662894 1880825208469897144079663 := by
  unfold tailWord_3662894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16699589948996010666992467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89064479727978723557293157 16699589948996010666992467)
  ·
    refine ⟨25049384923494016000488701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16699589948996010666992467 25049384923494016000488701)
    ·
      refine ⟨9393519346310256000183263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25049384923494016000488701 9393519346310256000183263)
      ·
        refine ⟨14090279019465384000274895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9393519346310256000183263 14090279019465384000274895)
        ·
          refine ⟨21135418529198076000412343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14090279019465384000274895 21135418529198076000412343)
          ·
            refine ⟨31703127793797114000618515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21135418529198076000412343 31703127793797114000618515)
            ·
              refine ⟨47554691690695671000927773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31703127793797114000618515 47554691690695671000927773)
              ·
                refine ⟨17833009384010876625347915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47554691690695671000927773 17833009384010876625347915)
                ·
                  refine ⟨26749514076016314938021873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17833009384010876625347915 26749514076016314938021873)
                  ·
                    refine ⟨20062135557012236203516405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26749514076016314938021873 20062135557012236203516405)
                    ·
                      refine ⟨1880825208469897144079663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20062135557012236203516405 1880825208469897144079663)
                      ·
                        rfl

theorem cell23_3662894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3662894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662894 prefixEnd_3662894 := by exact prefixLift 3662894
  have htrace : WordTrace (prefixWord ++ tailWord_3662894) baseStart_3662894 baseEnd_3662894 := by
    simpa [prefixWord, tailWord_3662894, baseEnd_3662894] using wordTrace_append hprefix tailTrace_3662894
  have hstable : (prefixWord ++ tailWord_3662894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662894).length < 2 ^ (prefixWord ++ tailWord_3662894).sum := by decide
  have hdescent : baseEnd_3662894 < baseStart_3662894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662918 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_3662918 : Nat := 118140960795 + 3662918 * 2 ^ 59
def prefixEnd_3662918 : Nat := 4983230072969 + 3 ^ 40 * 3662918 * 2
def baseEnd_3662918 : Nat := 626945844001868350059851

theorem tailTrace_3662918 : CollatzResearch.WordTrace tailWord_3662918 prefixEnd_3662918 626945844001868350059851 := by
  unfold tailWord_3662918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4174924841996285544837919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89065063295920758289875605 4174924841996285544837919)
  ·
    refine ⟨6262387262994428317256879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4174924841996285544837919 6262387262994428317256879)
    ·
      refine ⟨9393580894491642475885319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6262387262994428317256879 9393580894491642475885319)
      ·
        refine ⟨14090371341737463713827979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9393580894491642475885319 14090371341737463713827979)
        ·
          refine ⟨21135557012606195570741969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14090371341737463713827979 21135557012606195570741969)
          ·
            refine ⟨15851667759454646678056477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21135557012606195570741969 15851667759454646678056477)
            ·
              refine ⟨5944375409795492504271179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15851667759454646678056477 5944375409795492504271179)
              ·
                refine ⟨8916563114693238756406769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5944375409795492504271179 8916563114693238756406769)
                ·
                  refine ⟨6687422336019929067305077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8916563114693238756406769 6687422336019929067305077)
                  ·
                    refine ⟨626945844001868350059851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6687422336019929067305077 626945844001868350059851)
                    ·
                      rfl

theorem cell23_3662918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_3662918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662918 prefixEnd_3662918 := by exact prefixLift 3662918
  have htrace : WordTrace (prefixWord ++ tailWord_3662918) baseStart_3662918 baseEnd_3662918 := by
    simpa [prefixWord, tailWord_3662918, baseEnd_3662918] using wordTrace_append hprefix tailTrace_3662918
  have hstable : (prefixWord ++ tailWord_3662918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662918).length < 2 ^ (prefixWord ++ tailWord_3662918).sum := by decide
  have hdescent : baseEnd_3662918 < baseStart_3662918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662931 : List Nat := [1, 1, 1, 2, 1, 1, 2, 9, 1, 4]
def baseStart_3662931 : Nat := 118140960795 + 3662931 * 2 ^ 59
def prefixEnd_3662931 : Nat := 4983230072969 + 3 ^ 40 * 3662931 * 2
def baseEnd_3662931 : Nat := 626948069084704499772331

theorem tailTrace_3662931 : CollatzResearch.WordTrace tailWord_3662931 prefixEnd_3662931 626948069084704499772331 := by
  unfold tailWord_3662931
  simp only [CollatzResearch.WordTrace]
  refine ⟨133598069092834040655036647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89065379395222693770024431 133598069092834040655036647)
  ·
    refine ⟨200397103639251060982554971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133598069092834040655036647 200397103639251060982554971)
    ·
      refine ⟨300595655458876591473832457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200397103639251060982554971 300595655458876591473832457)
      ·
        refine ⟨225446741594157443605374343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300595655458876591473832457 225446741594157443605374343)
        ·
          refine ⟨338170112391236165408061515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225446741594157443605374343 338170112391236165408061515)
          ·
            refine ⟨507255168586854248112092273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338170112391236165408061515 507255168586854248112092273)
            ·
              refine ⟨380441376440140686084069205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507255168586854248112092273 380441376440140686084069205)
              ·
                refine ⟨2229148690078949332523843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 380441376440140686084069205 2229148690078949332523843)
                ·
                  refine ⟨3343723035118423998785765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229148690078949332523843 3343723035118423998785765)
                  ·
                    refine ⟨626948069084704499772331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3343723035118423998785765 626948069084704499772331)
                    ·
                      rfl

theorem cell23_3662931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 4].length) (baseStart_3662931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3662931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3662931 prefixEnd_3662931 := by exact prefixLift 3662931
  have htrace : WordTrace (prefixWord ++ tailWord_3662931) baseStart_3662931 baseEnd_3662931 := by
    simpa [prefixWord, tailWord_3662931, baseEnd_3662931] using wordTrace_append hprefix tailTrace_3662931
  have hstable : (prefixWord ++ tailWord_3662931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662931).length < 2 ^ (prefixWord ++ tailWord_3662931).sum := by decide
  have hdescent : baseEnd_3662931 < baseStart_3662931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663031 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_3663031 : Nat := 118140960795 + 3663031 * 2 ^ 59
def prefixEnd_3663031 : Nat := 4983230072969 + 3 ^ 40 * 3663031 * 2
def baseEnd_3663031 : Nat := 1880895555319563108066533

theorem tailTrace_3663031 : CollatzResearch.WordTrace tailWord_3663031 prefixEnd_3663031 1880895555319563108066533 := by
  unfold tailWord_3663031
  simp only [CollatzResearch.WordTrace]
  refine ⟨133601716392471757733676947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89067810928314505155784631 133601716392471757733676947)
  ·
    refine ⟨200402574588707636600515421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133601716392471757733676947 200402574588707636600515421)
    ·
      refine ⟨75150965470765363725193283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200402574588707636600515421 75150965470765363725193283)
      ·
        refine ⟨112726448206148045587789925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75150965470765363725193283 112726448206148045587789925)
        ·
          refine ⟨21136209038652758547710611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112726448206148045587789925 21136209038652758547710611)
          ·
            refine ⟨31704313557979137821565917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21136209038652758547710611 31704313557979137821565917)
            ·
              refine ⟨11889117584242176683087219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31704313557979137821565917 11889117584242176683087219)
              ·
                refine ⟨17833676376363265024630829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11889117584242176683087219 17833676376363265024630829)
                ·
                  refine ⟨6687628641136224384236561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17833676376363265024630829 6687628641136224384236561)
                  ·
                    refine ⟨5015721480852168288177421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6687628641136224384236561 5015721480852168288177421)
                    ·
                      refine ⟨1880895555319563108066533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5015721480852168288177421 1880895555319563108066533)
                      ·
                        rfl

theorem cell23_3663031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_3663031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663031 prefixEnd_3663031 := by exact prefixLift 3663031
  have htrace : WordTrace (prefixWord ++ tailWord_3663031) baseStart_3663031 baseEnd_3663031 := by
    simpa [prefixWord, tailWord_3663031, baseEnd_3663031] using wordTrace_append hprefix tailTrace_3663031
  have hstable : (prefixWord ++ tailWord_3663031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663031).length < 2 ^ (prefixWord ++ tailWord_3663031).sum := by decide
  have hdescent : baseEnd_3663031 < baseStart_3663031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663045 : List Nat := [1, 3, 1, 1, 1, 1, 3, 7, 1, 2, 2]
def baseStart_3663045 : Nat := 118140960795 + 3663045 * 2 ^ 59
def prefixEnd_3663045 : Nat := 4983230072969 + 3 ^ 40 * 3663045 * 2
def baseEnd_3663045 : Nat := 1880902744048726053291469

theorem tailTrace_3663045 : CollatzResearch.WordTrace tailWord_3663045 prefixEnd_3663045 1880902744048726053291469 := by
  unfold tailWord_3663045
  simp only [CollatzResearch.WordTrace]
  refine ⟨133602227014421038124686589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89068151342947358749791059 133602227014421038124686589)
  ·
    refine ⟨50100835130407889296757471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133602227014421038124686589 50100835130407889296757471)
    ·
      refine ⟨75151252695611833945136207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50100835130407889296757471 75151252695611833945136207)
      ·
        refine ⟨112726879043417750917704311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75151252695611833945136207 112726879043417750917704311)
        ·
          refine ⟨169090318565126626376556467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112726879043417750917704311 169090318565126626376556467)
          ·
            refine ⟨253635477847689939564834701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169090318565126626376556467 253635477847689939564834701)
            ·
              refine ⟨95113304192883727336813013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253635477847689939564834701 95113304192883727336813013)
              ·
                refine ⟨2229218067020712359456555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95113304192883727336813013 2229218067020712359456555)
                ·
                  refine ⟨3343827100531068539184833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229218067020712359456555 3343827100531068539184833)
                  ·
                    refine ⟨2507870325398301404388625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3343827100531068539184833 2507870325398301404388625)
                    ·
                      refine ⟨1880902744048726053291469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507870325398301404388625 1880902744048726053291469)
                      ·
                        rfl

theorem cell23_3663045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 2, 2].length) (baseStart_3663045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663045 prefixEnd_3663045 := by exact prefixLift 3663045
  have htrace : WordTrace (prefixWord ++ tailWord_3663045) baseStart_3663045 baseEnd_3663045 := by
    simpa [prefixWord, tailWord_3663045, baseEnd_3663045] using wordTrace_append hprefix tailTrace_3663045
  have hstable : (prefixWord ++ tailWord_3663045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663045).length < 2 ^ (prefixWord ++ tailWord_3663045).sum := by decide
  have hdescent : baseEnd_3663045 < baseStart_3663045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663104 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_3663104 : Nat := 118140960795 + 3663104 * 2 ^ 59
def prefixEnd_3663104 : Nat := 4983230072969 + 3 ^ 40 * 3663104 * 2
def baseEnd_3663104 : Nat := 1880933039407341322453697

theorem tailTrace_3663104 : CollatzResearch.WordTrace tailWord_3663104 prefixEnd_3663104 1880933039407341322453697 := by
  unfold tailWord_3663104
  simp only [CollatzResearch.WordTrace]
  refine ⟨66802189460603645600542183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89069585947471527467389577 66802189460603645600542183)
  ·
    refine ⟨100203284190905468400813275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66802189460603645600542183 100203284190905468400813275)
    ·
      refine ⟨150304926286358202601219913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100203284190905468400813275 150304926286358202601219913)
      ·
        refine ⟨112728694714768651950914935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150304926286358202601219913 112728694714768651950914935)
        ·
          refine ⟨169093042072152977926372403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112728694714768651950914935 169093042072152977926372403)
          ·
            refine ⟨253639563108229466889558605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169093042072152977926372403 253639563108229466889558605)
            ·
              refine ⟨95114836165586050083584477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253639563108229466889558605 95114836165586050083584477)
              ·
                refine ⟨35668063562094768781344179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95114836165586050083584477 35668063562094768781344179)
                ·
                  refine ⟨53502095343142153172016269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35668063562094768781344179 53502095343142153172016269)
                  ·
                    refine ⟨20063285753678307439506101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53502095343142153172016269 20063285753678307439506101)
                    ·
                      refine ⟨1880933039407341322453697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20063285753678307439506101 1880933039407341322453697)
                      ·
                        rfl

theorem cell23_3663104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_3663104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663104 prefixEnd_3663104 := by exact prefixLift 3663104
  have htrace : WordTrace (prefixWord ++ tailWord_3663104) baseStart_3663104 baseEnd_3663104 := by
    simpa [prefixWord, tailWord_3663104, baseEnd_3663104] using wordTrace_append hprefix tailTrace_3663104
  have hstable : (prefixWord ++ tailWord_3663104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663104).length < 2 ^ (prefixWord ++ tailWord_3663104).sum := by decide
  have hdescent : baseEnd_3663104 < baseStart_3663104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663105 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_3663105 : Nat := 118140960795 + 3663105 * 2 ^ 59
def prefixEnd_3663105 : Nat := 4983230072969 + 3 ^ 40 * 3663105 * 2
def baseEnd_3663105 : Nat := 1880933552887995818541193

theorem tailTrace_3663105 : CollatzResearch.WordTrace tailWord_3663105 prefixEnd_3663105 1880933552887995818541193 := by
  unfold tailWord_3663105
  simp only [CollatzResearch.WordTrace]
  refine ⟨133604415394203668371870769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89069610262802445581247179 133604415394203668371870769)
  ·
    refine ⟨100203311545652751278903077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133604415394203668371870769 100203311545652751278903077)
    ·
      refine ⟨18788120914809890864794327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100203311545652751278903077 18788120914809890864794327)
      ·
        refine ⟨28182181372214836297191491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18788120914809890864794327 28182181372214836297191491)
        ·
          refine ⟨42273272058322254445787237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28182181372214836297191491 42273272058322254445787237)
          ·
            refine ⟨7926238510935422708585107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42273272058322254445787237 7926238510935422708585107)
            ·
              refine ⟨11889357766403134062877661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926238510935422708585107 11889357766403134062877661)
              ·
                refine ⟨4458509162401175273579123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11889357766403134062877661 4458509162401175273579123)
                ·
                  refine ⟨6687763743601762910368685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4458509162401175273579123 6687763743601762910368685)
                  ·
                    refine ⟨2507911403850661091388257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6687763743601762910368685 2507911403850661091388257)
                    ·
                      refine ⟨1880933552887995818541193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507911403850661091388257 1880933552887995818541193)
                      ·
                        rfl

theorem cell23_3663105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_3663105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663105 prefixEnd_3663105 := by exact prefixLift 3663105
  have htrace : WordTrace (prefixWord ++ tailWord_3663105) baseStart_3663105 baseEnd_3663105 := by
    simpa [prefixWord, tailWord_3663105, baseEnd_3663105] using wordTrace_append hprefix tailTrace_3663105
  have hstable : (prefixWord ++ tailWord_3663105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663105).length < 2 ^ (prefixWord ++ tailWord_3663105).sum := by decide
  have hdescent : baseEnd_3663105 < baseStart_3663105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663112 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_3663112 : Nat := 118140960795 + 3663112 * 2 ^ 59
def prefixEnd_3663112 : Nat := 4983230072969 + 3 ^ 40 * 3663112 * 2
def baseEnd_3663112 : Nat := 1880937147252577291153661

theorem tailTrace_3663112 : CollatzResearch.WordTrace tailWord_3663112 prefixEnd_3663112 1880937147252577291153661 := by
  unfold tailWord_3663112
  simp only [CollatzResearch.WordTrace]
  refine ⟨66802335352589154283687795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89069780470118872378250393 66802335352589154283687795)
  ·
    refine ⟨100203503028883731425531693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66802335352589154283687795 100203503028883731425531693)
    ·
      refine ⟨37576313635831399284574385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100203503028883731425531693 37576313635831399284574385)
      ·
        refine ⟨28182235226873549463430789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37576313635831399284574385 28182235226873549463430789)
        ·
          refine ⟨5284169105038790524393273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28182235226873549463430789 5284169105038790524393273)
          ·
            refine ⟨3963126828779092893294955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5284169105038790524393273 3963126828779092893294955)
            ·
              refine ⟨5944690243168639339942433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963126828779092893294955 5944690243168639339942433)
              ·
                refine ⟨4458517682376479504956825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5944690243168639339942433 4458517682376479504956825)
                ·
                  refine ⟨3343888261782359628717619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4458517682376479504956825 3343888261782359628717619)
                  ·
                    refine ⟨5015832392673539443076429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3343888261782359628717619 5015832392673539443076429)
                    ·
                      refine ⟨1880937147252577291153661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5015832392673539443076429 1880937147252577291153661)
                      ·
                        rfl

theorem cell23_3663112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_3663112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663112 prefixEnd_3663112 := by exact prefixLift 3663112
  have htrace : WordTrace (prefixWord ++ tailWord_3663112) baseStart_3663112 baseEnd_3663112 := by
    simpa [prefixWord, tailWord_3663112, baseEnd_3663112] using wordTrace_append hprefix tailTrace_3663112
  have hstable : (prefixWord ++ tailWord_3663112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663112).length < 2 ^ (prefixWord ++ tailWord_3663112).sum := by decide
  have hdescent : baseEnd_3663112 < baseStart_3663112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663141 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 7]
def baseStart_3663141 : Nat := 118140960795 + 3663141 * 2 ^ 59
def prefixEnd_3663141 : Nat := 4983230072969 + 3 ^ 40 * 3663141 * 2
def baseEnd_3663141 : Nat := 208994670910173075299003

theorem tailTrace_3663141 : CollatzResearch.WordTrace tailWord_3663141 prefixEnd_3663141 208994670910173075299003 := by
  unfold tailWord_3663141
  simp only [CollatzResearch.WordTrace]
  refine ⟨133605728422073246520181277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89070485614715497680120851 133605728422073246520181277)
  ·
    refine ⟨50102148158277467445067979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133605728422073246520181277 50102148158277467445067979)
    ·
      refine ⟨75153222237416201167601969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50102148158277467445067979 75153222237416201167601969)
      ·
        refine ⟨56364916678062150875701477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75153222237416201167601969 56364916678062150875701477)
        ·
          refine ⟨10568421877136653289194027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56364916678062150875701477 10568421877136653289194027)
          ·
            refine ⟨15852632815704979933791041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10568421877136653289194027 15852632815704979933791041)
            ·
              refine ⟨11889474611778734950343281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15852632815704979933791041 11889474611778734950343281)
              ·
                refine ⟨8917105958834051212757461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11889474611778734950343281 8917105958834051212757461)
                ·
                  refine ⟨208994670910173075299003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8917105958834051212757461 208994670910173075299003)
                  ·
                    rfl

theorem cell23_3663141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_3663141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663141 prefixEnd_3663141 := by exact prefixLift 3663141
  have htrace : WordTrace (prefixWord ++ tailWord_3663141) baseStart_3663141 baseEnd_3663141 := by
    simpa [prefixWord, tailWord_3663141, baseEnd_3663141] using wordTrace_append hprefix tailTrace_3663141
  have hstable : (prefixWord ++ tailWord_3663141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663141).length < 2 ^ (prefixWord ++ tailWord_3663141).sum := by decide
  have hdescent : baseEnd_3663141 < baseStart_3663141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663175 : List Nat := [1, 1, 4, 1, 2, 4, 3, 2, 5]
def baseStart_3663175 : Nat := 118140960795 + 3663175 * 2 ^ 59
def prefixEnd_3663175 : Nat := 4983230072969 + 3 ^ 40 * 3663175 * 2
def baseEnd_3663175 : Nat := 208996610725978949407319

theorem tailTrace_3663175 : CollatzResearch.WordTrace tailWord_3663175 prefixEnd_3663175 208996610725978949407319 := by
  unfold tailWord_3663175
  simp only [CollatzResearch.WordTrace]
  refine ⟨133606968503950070326918979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89071312335966713551279319 133606968503950070326918979)
  ·
    refine ⟨200410452755925105490378469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133606968503950070326918979 200410452755925105490378469)
    ·
      refine ⟨37576959891735957279445963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200410452755925105490378469 37576959891735957279445963)
      ·
        refine ⟨56365439837603935919168945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37576959891735957279445963 56365439837603935919168945)
        ·
          refine ⟨42274079878202951939376709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56365439837603935919168945 42274079878202951939376709)
          ·
            refine ⟨7926389977163053488633133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42274079878202951939376709 7926389977163053488633133)
            ·
              refine ⟨2972396241436145058237425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7926389977163053488633133 2972396241436145058237425)
              ·
                refine ⟨2229297181077108793678069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2972396241436145058237425 2229297181077108793678069)
                ·
                  refine ⟨208996610725978949407319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2229297181077108793678069 208996610725978949407319)
                  ·
                    rfl

theorem cell23_3663175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 5].length) (baseStart_3663175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663175 prefixEnd_3663175 := by exact prefixLift 3663175
  have htrace : WordTrace (prefixWord ++ tailWord_3663175) baseStart_3663175 baseEnd_3663175 := by
    simpa [prefixWord, tailWord_3663175, baseEnd_3663175] using wordTrace_append hprefix tailTrace_3663175
  have hstable : (prefixWord ++ tailWord_3663175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663175).length < 2 ^ (prefixWord ++ tailWord_3663175).sum := by decide
  have hdescent : baseEnd_3663175 < baseStart_3663175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663190 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3663190 : Nat := 118140960795 + 3663190 * 2 ^ 59
def prefixEnd_3663190 : Nat := 4983230072969 + 3 ^ 40 * 3663190 * 2
def baseEnd_3663190 : Nat := 1880977198743627985978303

theorem tailTrace_3663190 : CollatzResearch.WordTrace tailWord_3663190 prefixEnd_3663190 1880977198743627985978303 := by
  unfold tailWord_3663190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8350469724930982993044689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89071677065930485259143349 8350469724930982993044689)
  ·
    refine ⟨6262852293698237244783517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8350469724930982993044689 6262852293698237244783517)
    ·
      refine ⟨2348569610136838966793819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6262852293698237244783517 2348569610136838966793819)
      ·
        refine ⟨3522854415205258450190729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348569610136838966793819 3522854415205258450190729)
        ·
          refine ⟨2642140811403943837643047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3522854415205258450190729 2642140811403943837643047)
          ·
            refine ⟨3963211217105915756464571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642140811403943837643047 3963211217105915756464571)
            ·
              refine ⟨5944816825658873634696857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963211217105915756464571 5944816825658873634696857)
              ·
                refine ⟨4458612619244155226022643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5944816825658873634696857 4458612619244155226022643)
                ·
                  refine ⟨6687918928866232839033965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4458612619244155226022643 6687918928866232839033965)
                  ·
                    refine ⟨2507969598324837314637737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6687918928866232839033965 2507969598324837314637737)
                    ·
                      refine ⟨1880977198743627985978303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2507969598324837314637737 1880977198743627985978303)
                      ·
                        rfl

theorem cell23_3663190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3663190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663190 prefixEnd_3663190 := by exact prefixLift 3663190
  have htrace : WordTrace (prefixWord ++ tailWord_3663190) baseStart_3663190 baseEnd_3663190 := by
    simpa [prefixWord, tailWord_3663190, baseEnd_3663190] using wordTrace_append hprefix tailTrace_3663190
  have hstable : (prefixWord ++ tailWord_3663190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663190).length < 2 ^ (prefixWord ++ tailWord_3663190).sum := by decide
  have hdescent : baseEnd_3663190 < baseStart_3663190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663228 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_3663228 : Nat := 118140960795 + 3663228 * 2 ^ 59
def prefixEnd_3663228 : Nat := 4983230072969 + 3 ^ 40 * 3663228 * 2
def baseEnd_3663228 : Nat := 1880996711008498837303127

theorem tailTrace_3663228 : CollatzResearch.WordTrace tailWord_3663228 prefixEnd_3663228 1880996711008498837303127 := by
  unfold tailWord_3663228
  simp only [CollatzResearch.WordTrace]
  refine ⟨66804450786379030189299169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89072601048505373585732225 66804450786379030189299169)
  ·
    refine ⟨50103338089784272641974377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66804450786379030189299169 50103338089784272641974377)
    ·
      refine ⟨37577503567338204481480783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50103338089784272641974377 37577503567338204481480783)
      ·
        refine ⟨56366255351007306722221175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37577503567338204481480783 56366255351007306722221175)
        ·
          refine ⟨84549383026510960083331763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56366255351007306722221175 84549383026510960083331763)
          ·
            refine ⟨126824074539766440124997645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84549383026510960083331763 126824074539766440124997645)
            ·
              refine ⟨47559027952412415046874117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126824074539766440124997645 47559027952412415046874117)
              ·
                refine ⟨8917317741077327821288897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47559027952412415046874117 8917317741077327821288897)
                ·
                  refine ⟨6687988305807995865966673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8917317741077327821288897 6687988305807995865966673)
                  ·
                    refine ⟨5015991229355996899475005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6687988305807995865966673 5015991229355996899475005)
                    ·
                      refine ⟨1880996711008498837303127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5015991229355996899475005 1880996711008498837303127)
                      ·
                        rfl

theorem cell23_3663228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_3663228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663228 prefixEnd_3663228 := by exact prefixLift 3663228
  have htrace : WordTrace (prefixWord ++ tailWord_3663228) baseStart_3663228 baseEnd_3663228 := by
    simpa [prefixWord, tailWord_3663228, baseEnd_3663228] using wordTrace_append hprefix tailTrace_3663228
  have hstable : (prefixWord ++ tailWord_3663228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663228).length < 2 ^ (prefixWord ++ tailWord_3663228).sum := by decide
  have hdescent : baseEnd_3663228 < baseStart_3663228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663262 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3663262 : Nat := 118140960795 + 3663262 * 2 ^ 59
def prefixEnd_3663262 : Nat := 4983230072969 + 3 ^ 40 * 3663262 * 2
def baseEnd_3663262 : Nat := 1881014169350751704277971

theorem tailTrace_3663262 : CollatzResearch.WordTrace tailWord_3663262 prefixEnd_3663262 1881014169350751704277971 := by
  unfold tailWord_3663262
  simp only [CollatzResearch.WordTrace]
  refine ⟨16701267706829360523167005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89073427769756589456890693 16701267706829360523167005)
  ·
    refine ⟨6262975390061010196187627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16701267706829360523167005 6262975390061010196187627)
    ·
      refine ⟨9394463085091515294281441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6262975390061010196187627 9394463085091515294281441)
      ·
        refine ⟨7045847313818636470711081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9394463085091515294281441 7045847313818636470711081)
        ·
          refine ⟨5284385485363977353033311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7045847313818636470711081 5284385485363977353033311)
          ·
            refine ⟨7926578228045966029549967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284385485363977353033311 7926578228045966029549967)
            ·
              refine ⟨11889867342068949044324951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926578228045966029549967 11889867342068949044324951)
              ·
                refine ⟨17834801013103423566487427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11889867342068949044324951 17834801013103423566487427)
                ·
                  refine ⟨26752201519655135349731141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17834801013103423566487427 26752201519655135349731141)
                  ·
                    refine ⟨5016037784935337878074589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26752201519655135349731141 5016037784935337878074589)
                    ·
                      refine ⟨1881014169350751704277971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5016037784935337878074589 1881014169350751704277971)
                      ·
                        rfl

theorem cell23_3663262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3663262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663262 prefixEnd_3663262 := by exact prefixLift 3663262
  have htrace : WordTrace (prefixWord ++ tailWord_3663262) baseStart_3663262 baseEnd_3663262 := by
    simpa [prefixWord, tailWord_3663262, baseEnd_3663262] using wordTrace_append hprefix tailTrace_3663262
  have hstable : (prefixWord ++ tailWord_3663262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663262).length < 2 ^ (prefixWord ++ tailWord_3663262).sum := by decide
  have hdescent : baseEnd_3663262 < baseStart_3663262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663325 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_3663325 : Nat := 118140960795 + 3663325 * 2 ^ 59
def prefixEnd_3663325 : Nat := 4983230072969 + 3 ^ 40 * 3663325 * 2
def baseEnd_3663325 : Nat := 627015506210661652596727

theorem tailTrace_3663325 : CollatzResearch.WordTrace tailWord_3663325 prefixEnd_3663325 627015506210661652596727 := by
  unfold tailWord_3663325
  simp only [CollatzResearch.WordTrace]
  refine ⟨133612439453406645944879429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89074959635604430629919619 133612439453406645944879429)
  ·
    refine ⟨25052332397513746114664893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133612439453406645944879429 25052332397513746114664893)
    ·
      refine ⟨9394624649067654792999335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25052332397513746114664893 9394624649067654792999335)
      ·
        refine ⟨14091936973601482189499003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394624649067654792999335 14091936973601482189499003)
        ·
          refine ⟨21137905460402223284248505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14091936973601482189499003 21137905460402223284248505)
          ·
            refine ⟨15853429095301667463186379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21137905460402223284248505 15853429095301667463186379)
            ·
              refine ⟨23780143642952501194779569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15853429095301667463186379 23780143642952501194779569)
              ·
                refine ⟨17835107732214375896084677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23780143642952501194779569 17835107732214375896084677)
                ·
                  refine ⟨3344082699790195480515877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17835107732214375896084677 3344082699790195480515877)
                  ·
                    refine ⟨627015506210661652596727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3344082699790195480515877 627015506210661652596727)
                    ·
                      rfl

theorem cell23_3663325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_3663325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663325 prefixEnd_3663325 := by exact prefixLift 3663325
  have htrace : WordTrace (prefixWord ++ tailWord_3663325) baseStart_3663325 baseEnd_3663325 := by
    simpa [prefixWord, tailWord_3663325, baseEnd_3663325] using wordTrace_append hprefix tailTrace_3663325
  have hstable : (prefixWord ++ tailWord_3663325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663325).length < 2 ^ (prefixWord ++ tailWord_3663325).sum := by decide
  have hdescent : baseEnd_3663325 < baseStart_3663325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663335 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3663335 : Nat := 118140960795 + 3663335 * 2 ^ 59
def prefixEnd_3663335 : Nat := 4983230072969 + 3 ^ 40 * 3663335 * 2
def baseEnd_3663335 : Nat := 1881051653438529918665135

theorem tailTrace_3663335 : CollatzResearch.WordTrace tailWord_3663335 prefixEnd_3663335 1881051653438529918665135 := by
  unfold tailWord_3663335
  simp only [CollatzResearch.WordTrace]
  refine ⟨133612804183370417652743459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89075202788913611768495639 133612804183370417652743459)
  ·
    refine ⟨200419206275055626479115189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133612804183370417652743459 200419206275055626479115189)
    ·
      refine ⟨18789300588286464982417049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200419206275055626479115189 18789300588286464982417049)
      ·
        refine ⟨14091975441214848736812787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18789300588286464982417049 14091975441214848736812787)
        ·
          refine ⟨21137963161822273105219181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14091975441214848736812787 21137963161822273105219181)
          ·
            refine ⟨7926736185683352414457193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21137963161822273105219181 7926736185683352414457193)
            ·
              refine ⟨5945052139262514310842895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7926736185683352414457193 5945052139262514310842895)
              ·
                refine ⟨8917578208893771466264343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945052139262514310842895 8917578208893771466264343)
                ·
                  refine ⟨13376367313340657199396515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8917578208893771466264343 13376367313340657199396515)
                  ·
                    refine ⟨20064550970010985799094773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13376367313340657199396515 20064550970010985799094773)
                    ·
                      refine ⟨1881051653438529918665135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20064550970010985799094773 1881051653438529918665135)
                      ·
                        rfl

theorem cell23_3663335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3663335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663335 prefixEnd_3663335 := by exact prefixLift 3663335
  have htrace : WordTrace (prefixWord ++ tailWord_3663335) baseStart_3663335 baseEnd_3663335 := by
    simpa [prefixWord, tailWord_3663335, baseEnd_3663335] using wordTrace_append hprefix tailTrace_3663335
  have hstable : (prefixWord ++ tailWord_3663335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663335).length < 2 ^ (prefixWord ++ tailWord_3663335).sum := by decide
  have hdescent : baseEnd_3663335 < baseStart_3663335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663366 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3663366 : Nat := 118140960795 + 3663366 * 2 ^ 59
def prefixEnd_3663366 : Nat := 4983230072969 + 3 ^ 40 * 3663366 * 2
def baseEnd_3663366 : Nat := 1881067571338819297377493

theorem tailTrace_3663366 : CollatzResearch.WordTrace tailWord_3663366 prefixEnd_3663366 1881067571338819297377493 := by
  unfold tailWord_3663366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175435463945565935847561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89075956564172073298081301 4175435463945565935847561)
  ·
    refine ⟨3131576597959174451885671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4175435463945565935847561 3131576597959174451885671)
    ·
      refine ⟨4697364896938761677828507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3131576597959174451885671 4697364896938761677828507)
      ·
        refine ⟨7046047345408142516742761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697364896938761677828507 7046047345408142516742761)
        ·
          refine ⟨5284535509056106887557071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7046047345408142516742761 5284535509056106887557071)
          ·
            refine ⟨7926803263584160331335607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284535509056106887557071 7926803263584160331335607)
            ·
              refine ⟨11890204895376240497003411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926803263584160331335607 11890204895376240497003411)
              ·
                refine ⟨17835307343064360745505117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890204895376240497003411 17835307343064360745505117)
                ·
                  refine ⟨6688240253649135279564419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17835307343064360745505117 6688240253649135279564419)
                  ·
                    refine ⟨10032360380473702919346629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6688240253649135279564419 10032360380473702919346629)
                    ·
                      refine ⟨1881067571338819297377493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10032360380473702919346629 1881067571338819297377493)
                      ·
                        rfl

theorem cell23_3663366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3663366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663366 prefixEnd_3663366 := by exact prefixLift 3663366
  have htrace : WordTrace (prefixWord ++ tailWord_3663366) baseStart_3663366 baseEnd_3663366 := by
    simpa [prefixWord, tailWord_3663366, baseEnd_3663366] using wordTrace_append hprefix tailTrace_3663366
  have hstable : (prefixWord ++ tailWord_3663366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663366).length < 2 ^ (prefixWord ++ tailWord_3663366).sum := by decide
  have hdescent : baseEnd_3663366 < baseStart_3663366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663400 : List Nat := [2, 1, 5, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3663400 : Nat := 118140960795 + 3663400 * 2 ^ 59
def prefixEnd_3663400 : Nat := 4983230072969 + 3 ^ 40 * 3663400 * 2
def baseEnd_3663400 : Nat := 1881085029681072164352337

theorem tailTrace_3663400 : CollatzResearch.WordTrace tailWord_3663400 prefixEnd_3663400 1881085029681072164352337 := by
  unfold tailWord_3663400
  simp only [CollatzResearch.WordTrace]
  refine ⟨66807587464067466876929827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89076783285423289169239769 66807587464067466876929827)
  ·
    refine ⟨100211381196101200315394741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66807587464067466876929827 100211381196101200315394741)
    ·
      refine ⟨9394816987134487529568257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100211381196101200315394741 9394816987134487529568257)
      ·
        refine ⟨7046112740350865647176193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9394816987134487529568257 7046112740350865647176193)
        ·
          refine ⟨5284584555263149235382145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7046112740350865647176193 5284584555263149235382145)
          ·
            refine ⟨3963438416447361926536609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5284584555263149235382145 3963438416447361926536609)
            ·
              refine ⟨2972578812335521444902457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3963438416447361926536609 2972578812335521444902457)
              ·
                refine ⟨2229434109251641083676843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2972578812335521444902457 2229434109251641083676843)
                ·
                  refine ⟨3344151163877461625515265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229434109251641083676843 3344151163877461625515265)
                  ·
                    refine ⟨2508113372908096219136449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3344151163877461625515265 2508113372908096219136449)
                    ·
                      refine ⟨1881085029681072164352337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2508113372908096219136449 1881085029681072164352337)
                      ·
                        rfl

theorem cell23_3663400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3663400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663400 prefixEnd_3663400 := by exact prefixLift 3663400
  have htrace : WordTrace (prefixWord ++ tailWord_3663400) baseStart_3663400 baseEnd_3663400 := by
    simpa [prefixWord, tailWord_3663400, baseEnd_3663400] using wordTrace_append hprefix tailTrace_3663400
  have hstable : (prefixWord ++ tailWord_3663400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663400).length < 2 ^ (prefixWord ++ tailWord_3663400).sum := by decide
  have hdescent : baseEnd_3663400 < baseStart_3663400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663425 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3663425 : Nat := 118140960795 + 3663425 * 2 ^ 59
def prefixEnd_3663425 : Nat := 4983230072969 + 3 ^ 40 * 3663425 * 2
def baseEnd_3663425 : Nat := 1881097866697434566539721

theorem tailTrace_3663425 : CollatzResearch.WordTrace tailWord_3663425 prefixEnd_3663425 1881097866697434566539721 := by
  unfold tailWord_3663425
  simp only [CollatzResearch.WordTrace]
  refine ⟨133616086753044363023519729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89077391168696242015679819 133616086753044363023519729)
  ·
    refine ⟨100212065064783272267639797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133616086753044363023519729 100212065064783272267639797)
    ·
      refine ⟨9394881099823431775091231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100212065064783272267639797 9394881099823431775091231)
      ·
        refine ⟨14092321649735147662636847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394881099823431775091231 14092321649735147662636847)
        ·
          refine ⟨21138482474602721493955271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14092321649735147662636847 21138482474602721493955271)
          ·
            refine ⟨31707723711904082240932907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21138482474602721493955271 31707723711904082240932907)
            ·
              refine ⟨47561585567856123361399361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31707723711904082240932907 47561585567856123361399361)
              ·
                refine ⟨35671189175892092521049521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47561585567856123361399361 35671189175892092521049521)
                ·
                  refine ⟨26753391881919069390787141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35671189175892092521049521 26753391881919069390787141)
                  ·
                    refine ⟨5016260977859825510772589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26753391881919069390787141 5016260977859825510772589)
                    ·
                      refine ⟨1881097866697434566539721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5016260977859825510772589 1881097866697434566539721)
                      ·
                        rfl

theorem cell23_3663425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3663425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663425 prefixEnd_3663425 := by exact prefixLift 3663425
  have htrace : WordTrace (prefixWord ++ tailWord_3663425) baseStart_3663425 baseEnd_3663425 := by
    simpa [prefixWord, tailWord_3663425, baseEnd_3663425] using wordTrace_append hprefix tailTrace_3663425
  have hstable : (prefixWord ++ tailWord_3663425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663425).length < 2 ^ (prefixWord ++ tailWord_3663425).sum := by decide
  have hdescent : baseEnd_3663425 < baseStart_3663425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663438 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3663438 : Nat := 118140960795 + 3663438 * 2 ^ 59
def prefixEnd_3663438 : Nat := 4983230072969 + 3 ^ 40 * 3663438 * 2
def baseEnd_3663438 : Nat := 1881104541945943015677161

theorem tailTrace_3663438 : CollatzResearch.WordTrace tailWord_3663438 prefixEnd_3663438 1881104541945943015677161 := by
  unfold tailWord_3663438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16702070112749658280467871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89077707267998177495828645 16702070112749658280467871)
  ·
    refine ⟨25053105169124487420701807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16702070112749658280467871 25053105169124487420701807)
    ·
      refine ⟨37579657753686731131052711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25053105169124487420701807 37579657753686731131052711)
      ·
        refine ⟨56369486630530096696579067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37579657753686731131052711 56369486630530096696579067)
        ·
          refine ⟨84554229945795145044868601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56369486630530096696579067 84554229945795145044868601)
          ·
            refine ⟨63415672459346358783651451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84554229945795145044868601 63415672459346358783651451)
            ·
              refine ⟨95123508689019538175477177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63415672459346358783651451 95123508689019538175477177)
              ·
                refine ⟨71342631516764653631607883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95123508689019538175477177 71342631516764653631607883)
                ·
                  refine ⟨107013947275146980447411825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71342631516764653631607883 107013947275146980447411825)
                  ·
                    refine ⟨80260460456360235335558869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107013947275146980447411825 80260460456360235335558869)
                    ·
                      refine ⟨1881104541945943015677161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80260460456360235335558869 1881104541945943015677161)
                      ·
                        rfl

theorem cell23_3663438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3663438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663438 prefixEnd_3663438 := by exact prefixLift 3663438
  have htrace : WordTrace (prefixWord ++ tailWord_3663438) baseStart_3663438 baseEnd_3663438 := by
    simpa [prefixWord, tailWord_3663438, baseEnd_3663438] using wordTrace_append hprefix tailTrace_3663438
  have hstable : (prefixWord ++ tailWord_3663438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663438).length < 2 ^ (prefixWord ++ tailWord_3663438).sum := by decide
  have hdescent : baseEnd_3663438 < baseStart_3663438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663465 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 1, 7, 2]
def baseStart_3663465 : Nat := 118140960795 + 3663465 * 2 ^ 59
def prefixEnd_3663465 : Nat := 4983230072969 + 3 ^ 40 * 3663465 * 2
def baseEnd_3663465 : Nat := 1881118405923614410039537

theorem tailTrace_3663465 : CollatzResearch.WordTrace tailWord_3663465 prefixEnd_3663465 1881118405923614410039537 := by
  unfold tailWord_3663465
  simp only [CollatzResearch.WordTrace]
  refine ⟨133617545672899449854975849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89078363781932966569983899 133617545672899449854975849)
  ·
    refine ⟨100213159254674587391231887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133617545672899449854975849 100213159254674587391231887)
    ·
      refine ⟨150319738882011881086847831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100213159254674587391231887 150319738882011881086847831)
      ·
        refine ⟨225479608323017821630271747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150319738882011881086847831 225479608323017821630271747)
        ·
          refine ⟨338219412484526732445407621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225479608323017821630271747 338219412484526732445407621)
          ·
            refine ⟨63416139840848762333513929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338219412484526732445407621 63416139840848762333513929)
            ·
              refine ⟨47562104880636571750135447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63416139840848762333513929 47562104880636571750135447)
              ·
                refine ⟨71343157320954857625203171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47562104880636571750135447 71343157320954857625203171)
                ·
                  refine ⟨107014735981432286437804757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71343157320954857625203171 107014735981432286437804757)
                  ·
                    refine ⟨2508157874564819213386049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 107014735981432286437804757 2508157874564819213386049)
                    ·
                      refine ⟨1881118405923614410039537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2508157874564819213386049 1881118405923614410039537)
                      ·
                        rfl

theorem cell23_3663465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 7, 2].length) (baseStart_3663465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663465 prefixEnd_3663465 := by exact prefixLift 3663465
  have htrace : WordTrace (prefixWord ++ tailWord_3663465) baseStart_3663465 baseEnd_3663465 := by
    simpa [prefixWord, tailWord_3663465, baseEnd_3663465] using wordTrace_append hprefix tailTrace_3663465
  have hstable : (prefixWord ++ tailWord_3663465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663465).length < 2 ^ (prefixWord ++ tailWord_3663465).sum := by decide
  have hdescent : baseEnd_3663465 < baseStart_3663465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663468 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_3663468 : Nat := 118140960795 + 3663468 * 2 ^ 59
def prefixEnd_3663468 : Nat := 4983230072969 + 3 ^ 40 * 3663468 * 2
def baseEnd_3663468 : Nat := 1881119946365577898302023

theorem tailTrace_3663468 : CollatzResearch.WordTrace tailWord_3663468 prefixEnd_3663468 1881119946365577898302023 := by
  unfold tailWord_3663468
  simp only [CollatzResearch.WordTrace]
  refine ⟨66808827545944290683667529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89078436727925720911556705 66808827545944290683667529)
  ·
    refine ⟨50106620659458218012750647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66808827545944290683667529 50106620659458218012750647)
    ·
      refine ⟨75159930989187327019125971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50106620659458218012750647 75159930989187327019125971)
      ·
        refine ⟨112739896483780990528688957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75159930989187327019125971 112739896483780990528688957)
        ·
          refine ⟨42277461181417871448258359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112739896483780990528688957 42277461181417871448258359)
          ·
            refine ⟨63416191772126807172387539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42277461181417871448258359 63416191772126807172387539)
            ·
              refine ⟨95124287658190210758581309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63416191772126807172387539 95124287658190210758581309)
              ·
                refine ⟨35671607871821329034467991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95124287658190210758581309 35671607871821329034467991)
                ·
                  refine ⟨53507411807731993551701987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35671607871821329034467991 53507411807731993551701987)
                  ·
                    refine ⟨80261117711597990327552981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53507411807731993551701987 80261117711597990327552981)
                    ·
                      refine ⟨1881119946365577898302023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80261117711597990327552981 1881119946365577898302023)
                      ·
                        rfl

theorem cell23_3663468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_3663468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663468 prefixEnd_3663468 := by exact prefixLift 3663468
  have htrace : WordTrace (prefixWord ++ tailWord_3663468) baseStart_3663468 baseEnd_3663468 := by
    simpa [prefixWord, tailWord_3663468, baseEnd_3663468] using wordTrace_append hprefix tailTrace_3663468
  have hstable : (prefixWord ++ tailWord_3663468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663468).length < 2 ^ (prefixWord ++ tailWord_3663468).sum := by decide
  have hdescent : baseEnd_3663468 < baseStart_3663468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663488 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 2, 8]
def baseStart_3663488 : Nat := 118140960795 + 3663488 * 2 ^ 59
def prefixEnd_3663488 : Nat := 4983230072969 + 3 ^ 40 * 3663488 * 2
def baseEnd_3663488 : Nat := 627043405326222606683977

theorem tailTrace_3663488 : CollatzResearch.WordTrace tailWord_3663488 prefixEnd_3663488 627043405326222606683977 := by
  unfold tailWord_3663488
  simp only [CollatzResearch.WordTrace]
  refine ⟨66809192275908062391531559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89078923034544083188708745 66809192275908062391531559)
  ·
    refine ⟨100213788413862093587297339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66809192275908062391531559 100213788413862093587297339)
    ·
      refine ⟨150320682620793140380946009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100213788413862093587297339 150320682620793140380946009)
      ·
        refine ⟨112740511965594855285709507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150320682620793140380946009 112740511965594855285709507)
        ·
          refine ⟨169110767948392282928564261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112740511965594855285709507 169110767948392282928564261)
          ·
            refine ⟨31708268990323553049105799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169110767948392282928564261 31708268990323553049105799)
            ·
              refine ⟨47562403485485329573658699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31708268990323553049105799 47562403485485329573658699)
              ·
                refine ⟨71343605228227994360488049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47562403485485329573658699 71343605228227994360488049)
                ·
                  refine ⟨53507703921170995770366037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71343605228227994360488049 53507703921170995770366037)
                  ·
                    refine ⟨627043405326222606683977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53507703921170995770366037 627043405326222606683977)
                    ·
                      rfl

theorem cell23_3663488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_3663488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663488 prefixEnd_3663488 := by exact prefixLift 3663488
  have htrace : WordTrace (prefixWord ++ tailWord_3663488) baseStart_3663488 baseEnd_3663488 := by
    simpa [prefixWord, tailWord_3663488, baseEnd_3663488] using wordTrace_append hprefix tailTrace_3663488
  have hstable : (prefixWord ++ tailWord_3663488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663488).length < 2 ^ (prefixWord ++ tailWord_3663488).sum := by decide
  have hdescent : baseEnd_3663488 < baseStart_3663488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663495 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_3663495 : Nat := 118140960795 + 3663495 * 2 ^ 59
def prefixEnd_3663495 : Nat := 4983230072969 + 3 ^ 40 * 3663495 * 2
def baseEnd_3663495 : Nat := 1881133810343249292664399

theorem tailTrace_3663495 : CollatzResearch.WordTrace tailWord_3663495 prefixEnd_3663495 1881133810343249292664399 := by
  unfold tailWord_3663495
  simp only [CollatzResearch.WordTrace]
  refine ⟨133618639862790764978567939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89079093241860509985711959 133618639862790764978567939)
  ·
    refine ⟨200427959794186147467851909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133618639862790764978567939 200427959794186147467851909)
    ·
      refine ⟨37580242461409902650222233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200427959794186147467851909 37580242461409902650222233)
      ·
        refine ⟨28185181846057426987666675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37580242461409902650222233 28185181846057426987666675)
        ·
          refine ⟨42277772769086140481500013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28185181846057426987666675 42277772769086140481500013)
          ·
            refine ⟨15854164788407302680562505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42277772769086140481500013 15854164788407302680562505)
            ·
              refine ⟨11890623591305477010421879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15854164788407302680562505 11890623591305477010421879)
              ·
                refine ⟨17835935386958215515632819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890623591305477010421879 17835935386958215515632819)
                ·
                  refine ⟨26753903080437323273449229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17835935386958215515632819 26753903080437323273449229)
                  ·
                    refine ⟨10032713655163996227543461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26753903080437323273449229 10032713655163996227543461)
                    ·
                      refine ⟨1881133810343249292664399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10032713655163996227543461 1881133810343249292664399)
                      ·
                        rfl

theorem cell23_3663495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_3663495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663495 prefixEnd_3663495 := by exact prefixLift 3663495
  have htrace : WordTrace (prefixWord ++ tailWord_3663495) baseStart_3663495 baseEnd_3663495 := by
    simpa [prefixWord, tailWord_3663495, baseEnd_3663495] using wordTrace_append hprefix tailTrace_3663495
  have hstable : (prefixWord ++ tailWord_3663495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663495).length < 2 ^ (prefixWord ++ tailWord_3663495).sum := by decide
  have hdescent : baseEnd_3663495 < baseStart_3663495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663496 : List Nat := [2, 1, 3, 5, 1, 2, 1, 3, 5]
def baseStart_3663496 : Nat := 118140960795 + 3663496 * 2 ^ 59
def prefixEnd_3663496 : Nat := 4983230072969 + 3 ^ 40 * 3663496 * 2
def baseEnd_3663496 : Nat := 209014924869322643194655

theorem tailTrace_3663496 : CollatzResearch.WordTrace tailWord_3663496 prefixEnd_3663496 209014924869322643194655 := by
  unfold tailWord_3663496
  simp only [CollatzResearch.WordTrace]
  refine ⟨66809338167893571074677171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89079117557191428099569561 66809338167893571074677171)
  ·
    refine ⟨100214007251840356612015757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66809338167893571074677171 100214007251840356612015757)
    ·
      refine ⟨37580252719440133729505909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100214007251840356612015757 37580252719440133729505909)
      ·
        refine ⟨3523148692447512537141179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37580252719440133729505909 3523148692447512537141179)
        ·
          refine ⟨5284723038671268805711769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523148692447512537141179 5284723038671268805711769)
          ·
            refine ⟨3963542279003451604283827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5284723038671268805711769 3963542279003451604283827)
            ·
              refine ⟨5945313418505177406425741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963542279003451604283827 5945313418505177406425741)
              ·
                refine ⟨2229492531939441527409653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5945313418505177406425741 2229492531939441527409653)
                ·
                  refine ⟨209014924869322643194655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2229492531939441527409653 209014924869322643194655)
                  ·
                    rfl

theorem cell23_3663496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 5].length) (baseStart_3663496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663496 prefixEnd_3663496 := by exact prefixLift 3663496
  have htrace : WordTrace (prefixWord ++ tailWord_3663496) baseStart_3663496 baseEnd_3663496 := by
    simpa [prefixWord, tailWord_3663496, baseEnd_3663496] using wordTrace_append hprefix tailTrace_3663496
  have hstable : (prefixWord ++ tailWord_3663496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663496).length < 2 ^ (prefixWord ++ tailWord_3663496).sum := by decide
  have hdescent : baseEnd_3663496 < baseStart_3663496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663512 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3663512 : Nat := 118140960795 + 3663512 * 2 ^ 59
def prefixEnd_3663512 : Nat := 4983230072969 + 3 ^ 40 * 3663512 * 2
def baseEnd_3663512 : Nat := 1881142539514375726151821

theorem tailTrace_3663512 : CollatzResearch.WordTrace tailWord_3663512 prefixEnd_3663512 1881142539514375726151821 := by
  unfold tailWord_3663512
  simp only [CollatzResearch.WordTrace]
  refine ⟨66809629951864588440968395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89079506602486117921291193 66809629951864588440968395)
  ·
    refine ⟨100214444927796882661452593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66809629951864588440968395 100214444927796882661452593)
    ·
      refine ⟨75160833695847661996089445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100214444927796882661452593 75160833695847661996089445)
      ·
        refine ⟨14092656317971436624266771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75160833695847661996089445 14092656317971436624266771)
        ·
          refine ⟨21138984476957154936400157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14092656317971436624266771 21138984476957154936400157)
          ·
            refine ⟨7927119178858933101150059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21138984476957154936400157 7927119178858933101150059)
            ·
              refine ⟨11890678768288399651725089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927119178858933101150059 11890678768288399651725089)
              ·
                refine ⟨8918009076216299738793817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11890678768288399651725089 8918009076216299738793817)
                ·
                  refine ⟨6688506807162224804095363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8918009076216299738793817 6688506807162224804095363)
                  ·
                    refine ⟨10032760210743337206143045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6688506807162224804095363 10032760210743337206143045)
                    ·
                      refine ⟨1881142539514375726151821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10032760210743337206143045 1881142539514375726151821)
                      ·
                        rfl

theorem cell23_3663512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3663512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663512 prefixEnd_3663512 := by exact prefixLift 3663512
  have htrace : WordTrace (prefixWord ++ tailWord_3663512) baseStart_3663512 baseEnd_3663512 := by
    simpa [prefixWord, tailWord_3663512, baseEnd_3663512] using wordTrace_append hprefix tailTrace_3663512
  have hstable : (prefixWord ++ tailWord_3663512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663512).length < 2 ^ (prefixWord ++ tailWord_3663512).sum := by decide
  have hdescent : baseEnd_3663512 < baseStart_3663512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663535 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 6]
def baseStart_3663535 : Nat := 118140960795 + 3663535 * 2 ^ 59
def prefixEnd_3663535 : Nat := 4983230072969 + 3 ^ 40 * 3663535 * 2
def baseEnd_3663535 : Nat := 209017149952158792907135

theorem tailTrace_3663535 : CollatzResearch.WordTrace tailWord_3663535 prefixEnd_3663535 209017149952158792907135 := by
  unfold tailWord_3663535
  simp only [CollatzResearch.WordTrace]
  refine ⟨133620098782645851810024059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89080065855097234540016039 133620098782645851810024059)
  ·
    refine ⟨200430148173968777715036089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133620098782645851810024059 200430148173968777715036089)
    ·
      refine ⟨150322611130476583286277067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200430148173968777715036089 150322611130476583286277067)
      ·
        refine ⟨225483916695714874929415601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150322611130476583286277067 225483916695714874929415601)
        ·
          refine ⟨169112937521786156197061701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225483916695714874929415601 169112937521786156197061701)
          ·
            refine ⟨31708675785334904286949069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169112937521786156197061701 31708675785334904286949069)
            ·
              refine ⟨11890753419500589107605901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31708675785334904286949069 11890753419500589107605901)
              ·
                refine ⟨4459032532312720915352213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11890753419500589107605901 4459032532312720915352213)
                ·
                  refine ⟨209017149952158792907135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4459032532312720915352213 209017149952158792907135)
                  ·
                    rfl

theorem cell23_3663535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 6].length) (baseStart_3663535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663535 prefixEnd_3663535 := by exact prefixLift 3663535
  have htrace : WordTrace (prefixWord ++ tailWord_3663535) baseStart_3663535 baseEnd_3663535 := by
    simpa [prefixWord, tailWord_3663535, baseEnd_3663535] using wordTrace_append hprefix tailTrace_3663535
  have hstable : (prefixWord ++ tailWord_3663535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663535).length < 2 ^ (prefixWord ++ tailWord_3663535).sum := by decide
  have hdescent : baseEnd_3663535 < baseStart_3663535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663545 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3663545 : Nat := 118140960795 + 3663545 * 2 ^ 59
def prefixEnd_3663545 : Nat := 4983230072969 + 3 ^ 40 * 3663545 * 2
def baseEnd_3663545 : Nat := 1881159484375974097039169

theorem tailTrace_3663545 : CollatzResearch.WordTrace tailWord_3663545 prefixEnd_3663545 1881159484375974097039169 := by
  unfold tailWord_3663545
  simp only [CollatzResearch.WordTrace]
  refine ⟨133620463512609623517888089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89080309008406415678592059 133620463512609623517888089)
  ·
    refine ⟨100215347634457217638416067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133620463512609623517888089 100215347634457217638416067)
    ·
      refine ⟨150323021451685826457624101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100215347634457217638416067 150323021451685826457624101)
      ·
        refine ⟨28185566522191092460804519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150323021451685826457624101 28185566522191092460804519)
        ·
          refine ⟨42278349783286638691206779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28185566522191092460804519 42278349783286638691206779)
          ·
            refine ⟨63417524674929958036810169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42278349783286638691206779 63417524674929958036810169)
            ·
              refine ⟨47563143506197468527607627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63417524674929958036810169 47563143506197468527607627)
              ·
                refine ⟨71344715259296202791411441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47563143506197468527607627 71344715259296202791411441)
                ·
                  refine ⟨53508536444472152093558581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71344715259296202791411441 53508536444472152093558581)
                  ·
                    refine ⟨5016425291669264258771117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53508536444472152093558581 5016425291669264258771117)
                    ·
                      refine ⟨1881159484375974097039169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5016425291669264258771117 1881159484375974097039169)
                      ·
                        rfl

theorem cell23_3663545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3663545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663545 prefixEnd_3663545 := by exact prefixLift 3663545
  have htrace : WordTrace (prefixWord ++ tailWord_3663545) baseStart_3663545 baseEnd_3663545 := by
    simpa [prefixWord, tailWord_3663545, baseEnd_3663545] using wordTrace_append hprefix tailTrace_3663545
  have hstable : (prefixWord ++ tailWord_3663545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663545).length < 2 ^ (prefixWord ++ tailWord_3663545).sum := by decide
  have hdescent : baseEnd_3663545 < baseStart_3663545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663595 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 1, 6]
def baseStart_3663595 : Nat := 118140960795 + 3663595 * 2 ^ 59
def prefixEnd_3663595 : Nat := 4983230072969 + 3 ^ 40 * 3663595 * 2
def baseEnd_3663595 : Nat := 627061719469566300471313

theorem tailTrace_3663595 : CollatzResearch.WordTrace tailWord_3663595 prefixEnd_3663595 627061719469566300471313 := by
  unfold tailWord_3663595
  simp only [CollatzResearch.WordTrace]
  refine ⟨133622287162428482057208239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89081524774952321371472159 133622287162428482057208239)
  ·
    refine ⟨200433430743642723085812359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133622287162428482057208239 200433430743642723085812359)
    ·
      refine ⟨300650146115464084628718539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200433430743642723085812359 300650146115464084628718539)
      ·
        refine ⟨450975219173196126943077809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300650146115464084628718539 450975219173196126943077809)
        ·
          refine ⟨338231414379897095207308357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450975219173196126943077809 338231414379897095207308357)
          ·
            refine ⟨63418390196230705351370317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338231414379897095207308357 63418390196230705351370317)
            ·
              refine ⟨23781896323586514506763869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63418390196230705351370317 23781896323586514506763869)
              ·
                refine ⟨8918211121344942940036451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23781896323586514506763869 8918211121344942940036451)
                ·
                  refine ⟨13377316682017414410054677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8918211121344942940036451 13377316682017414410054677)
                  ·
                    refine ⟨627061719469566300471313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13377316682017414410054677 627061719469566300471313)
                    ·
                      rfl

theorem cell23_3663595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 6].length) (baseStart_3663595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663595 prefixEnd_3663595 := by exact prefixLift 3663595
  have htrace : WordTrace (prefixWord ++ tailWord_3663595) baseStart_3663595 baseEnd_3663595 := by
    simpa [prefixWord, tailWord_3663595, baseEnd_3663595] using wordTrace_append hprefix tailTrace_3663595
  have hstable : (prefixWord ++ tailWord_3663595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663595).length < 2 ^ (prefixWord ++ tailWord_3663595).sum := by decide
  have hdescent : baseEnd_3663595 < baseStart_3663595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663602 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3663602 : Nat := 118140960795 + 3663602 * 2 ^ 59
def prefixEnd_3663602 : Nat := 4983230072969 + 3 ^ 40 * 3663602 * 2
def baseEnd_3663602 : Nat := 1881188752773280374026407

theorem tailTrace_3663602 : CollatzResearch.WordTrace tailWord_3663602 prefixEnd_3663602 1881188752773280374026407 := by
  unfold tailWord_3663602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33405635618350780563178265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89081694982268748168475373 33405635618350780563178265)
  ·
    refine ⟨25054226713763085422383699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33405635618350780563178265 25054226713763085422383699)
    ·
      refine ⟨37581340070644628133575549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25054226713763085422383699 37581340070644628133575549)
      ·
        refine ⟨14093002526491735550090831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37581340070644628133575549 14093002526491735550090831)
        ·
          refine ⟨21139503789737603325136247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14093002526491735550090831 21139503789737603325136247)
          ·
            refine ⟨31709255684606404987704371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21139503789737603325136247 31709255684606404987704371)
            ·
              refine ⟨47563883526909607481556557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31709255684606404987704371 47563883526909607481556557)
              ·
                refine ⟨17836456322591102805583709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47563883526909607481556557 17836456322591102805583709)
                ·
                  refine ⟨6688671120971663552093891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17836456322591102805583709 6688671120971663552093891)
                  ·
                    refine ⟨10033006681457495328140837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6688671120971663552093891 10033006681457495328140837)
                    ·
                      refine ⟨1881188752773280374026407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10033006681457495328140837 1881188752773280374026407)
                      ·
                        rfl

theorem cell23_3663602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3663602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663602 prefixEnd_3663602 := by exact prefixLift 3663602
  have htrace : WordTrace (prefixWord ++ tailWord_3663602) baseStart_3663602 baseEnd_3663602 := by
    simpa [prefixWord, tailWord_3663602, baseEnd_3663602] using wordTrace_append hprefix tailTrace_3663602
  have hstable : (prefixWord ++ tailWord_3663602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663602).length < 2 ^ (prefixWord ++ tailWord_3663602).sum := by decide
  have hdescent : baseEnd_3663602 < baseStart_3663602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663606 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_3663606 : Nat := 118140960795 + 3663606 * 2 ^ 59
def prefixEnd_3663606 : Nat := 4983230072969 + 3 ^ 40 * 3663606 * 2
def baseEnd_3663606 : Nat := 1881190806695898358376389

theorem tailTrace_3663606 : CollatzResearch.WordTrace tailWord_3663606 prefixEnd_3663606 1881190806695898358376389 := by
  unfold tailWord_3663606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351418022836789433491167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89081792243592420623905781 8351418022836789433491167)
  ·
    refine ⟨12527127034255184150236751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8351418022836789433491167 12527127034255184150236751)
    ·
      refine ⟨18790690551382776225355127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12527127034255184150236751 18790690551382776225355127)
      ·
        refine ⟨28186035827074164338032691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18790690551382776225355127 28186035827074164338032691)
        ·
          refine ⟨42279053740611246507049037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28186035827074164338032691 42279053740611246507049037)
          ·
            refine ⟨15854645152729217440143389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42279053740611246507049037 15854645152729217440143389)
            ·
              refine ⟨5945491932273456540053771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15854645152729217440143389 5945491932273456540053771)
              ·
                refine ⟨8918237898410184810080657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945491932273456540053771 8918237898410184810080657)
                ·
                  refine ⟨6688678423807638607560493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8918237898410184810080657 6688678423807638607560493)
                  ·
                    refine ⟨2508254408927864477835185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6688678423807638607560493 2508254408927864477835185)
                    ·
                      refine ⟨1881190806695898358376389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2508254408927864477835185 1881190806695898358376389)
                      ·
                        rfl

theorem cell23_3663606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_3663606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663606 prefixEnd_3663606 := by exact prefixLift 3663606
  have htrace : WordTrace (prefixWord ++ tailWord_3663606) baseStart_3663606 baseEnd_3663606 := by
    simpa [prefixWord, tailWord_3663606, baseEnd_3663606] using wordTrace_append hprefix tailTrace_3663606
  have hstable : (prefixWord ++ tailWord_3663606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663606).length < 2 ^ (prefixWord ++ tailWord_3663606).sum := by decide
  have hdescent : baseEnd_3663606 < baseStart_3663606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663612 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_3663612 : Nat := 118140960795 + 3663612 * 2 ^ 59
def prefixEnd_3663612 : Nat := 4983230072969 + 3 ^ 40 * 3663612 * 2
def baseEnd_3663612 : Nat := 627064629193275111633787

theorem tailTrace_3663612 : CollatzResearch.WordTrace tailWord_3663612 prefixEnd_3663612 627064629193275111633787 := by
  unfold tailWord_3663612
  simp only [CollatzResearch.WordTrace]
  refine ⟨66811453601683446980288545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89081938135577929307051393 66811453601683446980288545)
  ·
    refine ⟨50108590201262585235216409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66811453601683446980288545 50108590201262585235216409)
    ·
      refine ⟨37581442650946938926412307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50108590201262585235216409 37581442650946938926412307)
      ·
        refine ⟨56372163976420408389618461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37581442650946938926412307 56372163976420408389618461)
        ·
          refine ⟨21139561491157653146106923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56372163976420408389618461 21139561491157653146106923)
          ·
            refine ⟨31709342236736479719160385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21139561491157653146106923 31709342236736479719160385)
            ·
              refine ⟨23782006677552359789370289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31709342236736479719160385 23782006677552359789370289)
              ·
                refine ⟨17836505008164269842027717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23782006677552359789370289 17836505008164269842027717)
                ·
                  refine ⟨3344344689030800595380197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17836505008164269842027717 3344344689030800595380197)
                  ·
                    refine ⟨627064629193275111633787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3344344689030800595380197 627064629193275111633787)
                    ·
                      rfl

theorem cell23_3663612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_3663612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663612 prefixEnd_3663612 := by exact prefixLift 3663612
  have htrace : WordTrace (prefixWord ++ tailWord_3663612) baseStart_3663612 baseEnd_3663612 := by
    simpa [prefixWord, tailWord_3663612, baseEnd_3663612] using wordTrace_append hprefix tailTrace_3663612
  have hstable : (prefixWord ++ tailWord_3663612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663612).length < 2 ^ (prefixWord ++ tailWord_3663612).sum := by decide
  have hdescent : baseEnd_3663612 < baseStart_3663612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663619 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 1, 1, 4]
def baseStart_3663619 : Nat := 118140960795 + 3663619 * 2 ^ 59
def prefixEnd_3663619 : Nat := 4983230072969 + 3 ^ 40 * 3663619 * 2
def baseEnd_3663619 : Nat := 1881197481944406807513829

theorem tailTrace_3663619 : CollatzResearch.WordTrace tailWord_3663619 prefixEnd_3663619 1881197481944406807513829 := by
  unfold tailWord_3663619
  simp only [CollatzResearch.WordTrace]
  refine ⟨133623162514341534156081911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89082108342894356104054607 133623162514341534156081911)
  ·
    refine ⟨200434743771512301234122867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133623162514341534156081911 200434743771512301234122867)
    ·
      refine ⟨300652115657268451851184301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200434743771512301234122867 300652115657268451851184301)
      ·
        refine ⟨112744543371475669444194113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300652115657268451851184301 112744543371475669444194113)
        ·
          refine ⟨84558407528606752083145585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112744543371475669444194113 84558407528606752083145585)
          ·
            refine ⟨63418805646455064062359189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84558407528606752083145585 63418805646455064062359189)
            ·
              refine ⟨2972756514677581127923087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63418805646455064062359189 2972756514677581127923087)
              ·
                refine ⟨4459134772016371691884631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2972756514677581127923087 4459134772016371691884631)
                ·
                  refine ⟨6688702158024557537826947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459134772016371691884631 6688702158024557537826947)
                  ·
                    refine ⟨10033053237036836306740421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6688702158024557537826947 10033053237036836306740421)
                    ·
                      refine ⟨1881197481944406807513829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10033053237036836306740421 1881197481944406807513829)
                      ·
                        rfl

theorem cell23_3663619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_3663619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663619 prefixEnd_3663619 := by exact prefixLift 3663619
  have htrace : WordTrace (prefixWord ++ tailWord_3663619) baseStart_3663619 baseEnd_3663619 := by
    simpa [prefixWord, tailWord_3663619, baseEnd_3663619] using wordTrace_append hprefix tailTrace_3663619
  have hstable : (prefixWord ++ tailWord_3663619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663619).length < 2 ^ (prefixWord ++ tailWord_3663619).sum := by decide
  have hdescent : baseEnd_3663619 < baseStart_3663619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663649 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3663649 : Nat := 118140960795 + 3663649 * 2 ^ 59
def prefixEnd_3663649 : Nat := 4983230072969 + 3 ^ 40 * 3663649 * 2
def baseEnd_3663649 : Nat := 1881212886364041690138691

theorem tailTrace_3663649 : CollatzResearch.WordTrace tailWord_3663649 prefixEnd_3663649 1881212886364041690138691 := by
  unfold tailWord_3663649
  simp only [CollatzResearch.WordTrace]
  refine ⟨133624256704232849279674001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89082837802821899519782667 133624256704232849279674001)
  ·
    refine ⟨100218192528174636959755501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133624256704232849279674001 100218192528174636959755501)
    ·
      refine ⟨37581822198065488859908313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100218192528174636959755501 37581822198065488859908313)
      ·
        refine ⟨28186366648549116644931235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37581822198065488859908313 28186366648549116644931235)
        ·
          refine ⟨42279549972823674967396853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28186366648549116644931235 42279549972823674967396853)
          ·
            refine ⟨3963707809952219528193455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42279549972823674967396853 3963707809952219528193455)
            ·
              refine ⟨5945561714928329292290183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963707809952219528193455 5945561714928329292290183)
              ·
                refine ⟨8918342572392493938435275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945561714928329292290183 8918342572392493938435275)
                ·
                  refine ⟨13377513858588740907652913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8918342572392493938435275 13377513858588740907652913)
                  ·
                    refine ⟨10033135393941555680739685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13377513858588740907652913 10033135393941555680739685)
                    ·
                      refine ⟨1881212886364041690138691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10033135393941555680739685 1881212886364041690138691)
                      ·
                        rfl

theorem cell23_3663649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3663649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663649 prefixEnd_3663649 := by exact prefixLift 3663649
  have htrace : WordTrace (prefixWord ++ tailWord_3663649) baseStart_3663649 baseEnd_3663649 := by
    simpa [prefixWord, tailWord_3663649, baseEnd_3663649] using wordTrace_append hprefix tailTrace_3663649
  have hstable : (prefixWord ++ tailWord_3663649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663649).length < 2 ^ (prefixWord ++ tailWord_3663649).sum := by decide
  have hdescent : baseEnd_3663649 < baseStart_3663649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663656 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3663656 : Nat := 118140960795 + 3663656 * 2 ^ 59
def prefixEnd_3663656 : Nat := 4983230072969 + 3 ^ 40 * 3663656 * 2
def baseEnd_3663656 : Nat := 1881216480728623162751159

theorem tailTrace_3663656 : CollatzResearch.WordTrace tailWord_3663656 prefixEnd_3663656 1881216480728623162751159 := by
  unfold tailWord_3663656
  simp only [CollatzResearch.WordTrace]
  refine ⟨66812256007603744737589411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89083008010138326316785881 66812256007603744737589411)
  ·
    refine ⟨100218384011405617106384117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66812256007603744737589411 100218384011405617106384117)
    ·
      refine ⟨9395473501069276603723511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100218384011405617106384117 9395473501069276603723511)
      ·
        refine ⟨14093210251603914905585267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9395473501069276603723511 14093210251603914905585267)
        ·
          refine ⟨21139815377405872358377901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14093210251603914905585267 21139815377405872358377901)
          ·
            refine ⟨7927430766527202134391713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21139815377405872358377901 7927430766527202134391713)
            ·
              refine ⟨5945573074895401600793785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7927430766527202134391713 5945573074895401600793785)
              ·
                refine ⟨4459179806171551200595339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945573074895401600793785 4459179806171551200595339)
                ·
                  refine ⟨6688769709257326800893009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459179806171551200595339 6688769709257326800893009)
                  ·
                    refine ⟨5016577281942995100669757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6688769709257326800893009 5016577281942995100669757)
                    ·
                      refine ⟨1881216480728623162751159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5016577281942995100669757 1881216480728623162751159)
                      ·
                        rfl

theorem cell23_3663656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3663656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663656 prefixEnd_3663656 := by exact prefixLift 3663656
  have htrace : WordTrace (prefixWord ++ tailWord_3663656) baseStart_3663656 baseEnd_3663656 := by
    simpa [prefixWord, tailWord_3663656, baseEnd_3663656] using wordTrace_append hprefix tailTrace_3663656
  have hstable : (prefixWord ++ tailWord_3663656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663656).length < 2 ^ (prefixWord ++ tailWord_3663656).sum := by decide
  have hdescent : baseEnd_3663656 < baseStart_3663656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663712 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_3663712 : Nat := 118140960795 + 3663712 * 2 ^ 59
def prefixEnd_3663712 : Nat := 4983230072969 + 3 ^ 40 * 3663712 * 2
def baseEnd_3663712 : Nat := 1881245235645274943650901

theorem tailTrace_3663712 : CollatzResearch.WordTrace tailWord_3663712 prefixEnd_3663712 1881245235645274943650901 := by
  unfold tailWord_3663712
  simp only [CollatzResearch.WordTrace]
  refine ⟨66813277251502305519608695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89084369668669740692811593 66813277251502305519608695)
  ·
    refine ⟨100219915877253458279413043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66813277251502305519608695 100219915877253458279413043)
    ·
      refine ⟨150329873815880187419119565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100219915877253458279413043 150329873815880187419119565)
      ·
        refine ⟨56373702680955070282169837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150329873815880187419119565 56373702680955070282169837)
        ·
          refine ⟨21140138505358151355813689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56373702680955070282169837 21140138505358151355813689)
          ·
            refine ⟨15855103879018613516860267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21140138505358151355813689 15855103879018613516860267)
            ·
              refine ⟨23782655818527920275290401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15855103879018613516860267 23782655818527920275290401)
              ·
                refine ⟨17836991863895940206467801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23782655818527920275290401 17836991863895940206467801)
                ·
                  refine ⟨13377743897921955154850851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17836991863895940206467801 13377743897921955154850851)
                  ·
                    refine ⟨20066615846882932732276277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13377743897921955154850851 20066615846882932732276277)
                    ·
                      refine ⟨1881245235645274943650901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20066615846882932732276277 1881245235645274943650901)
                      ·
                        rfl

theorem cell23_3663712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_3663712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663712 prefixEnd_3663712 := by exact prefixLift 3663712
  have htrace : WordTrace (prefixWord ++ tailWord_3663712) baseStart_3663712 baseEnd_3663712 := by
    simpa [prefixWord, tailWord_3663712, baseEnd_3663712] using wordTrace_append hprefix tailTrace_3663712
  have hstable : (prefixWord ++ tailWord_3663712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663712).length < 2 ^ (prefixWord ++ tailWord_3663712).sum := by decide
  have hdescent : baseEnd_3663712 < baseStart_3663712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663726 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_3663726 : Nat := 118140960795 + 3663726 * 2 ^ 59
def prefixEnd_3663726 : Nat := 4983230072969 + 3 ^ 40 * 3663726 * 2
def baseEnd_3663726 : Nat := 1881252424374437888875837

theorem tailTrace_3663726 : CollatzResearch.WordTrace tailWord_3663726 prefixEnd_3663726 1881252424374437888875837 := by
  unfold tailWord_3663726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16703383140619236428778379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89084710083302594286818021 16703383140619236428778379)
  ·
    refine ⟨25055074710928854643167569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16703383140619236428778379 25055074710928854643167569)
    ·
      refine ⟨18791306033196640982375677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25055074710928854643167569 18791306033196640982375677)
      ·
        refine ⟨7046739762448740368390879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18791306033196640982375677 7046739762448740368390879)
        ·
          refine ⟨10570109643673110552586319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7046739762448740368390879 10570109643673110552586319)
          ·
            refine ⟨15855164465509665828879479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10570109643673110552586319 15855164465509665828879479)
            ·
              refine ⟨23782746698264498743319219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15855164465509665828879479 23782746698264498743319219)
              ·
                refine ⟨35674120047396748114978829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23782746698264498743319219 35674120047396748114978829)
                ·
                  refine ⟨13377795017773780543117061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35674120047396748114978829 13377795017773780543117061)
                  ·
                    refine ⟨2508336565832583851834449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13377795017773780543117061 2508336565832583851834449)
                    ·
                      refine ⟨1881252424374437888875837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2508336565832583851834449 1881252424374437888875837)
                      ·
                        rfl

theorem cell23_3663726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_3663726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663726 prefixEnd_3663726 := by exact prefixLift 3663726
  have htrace : WordTrace (prefixWord ++ tailWord_3663726) baseStart_3663726 baseEnd_3663726 := by
    simpa [prefixWord, tailWord_3663726, baseEnd_3663726] using wordTrace_append hprefix tailTrace_3663726
  have hstable : (prefixWord ++ tailWord_3663726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663726).length < 2 ^ (prefixWord ++ tailWord_3663726).sum := by decide
  have hdescent : baseEnd_3663726 < baseStart_3663726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663749 : List Nat := [1, 3, 1, 1, 3, 2, 3, 4, 5]
def baseStart_3663749 : Nat := 118140960795 + 3663749 * 2 ^ 59
def prefixEnd_3663749 : Nat := 4983230072969 + 3 ^ 40 * 3663749 * 2
def baseEnd_3663749 : Nat := 209029359381054588765359

theorem tailTrace_3663749 : CollatzResearch.WordTrace tailWord_3663749 prefixEnd_3663749 209029359381054588765359 := by
  unfold tailWord_3663749
  simp only [CollatzResearch.WordTrace]
  refine ⟨133627904003870566358314301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89085269335913710905542867 133627904003870566358314301)
  ·
    refine ⟨50110464001451462384367863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133627904003870566358314301 50110464001451462384367863)
    ·
      refine ⟨75165696002177193576551795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50110464001451462384367863 75165696002177193576551795)
      ·
        refine ⟨112748544003265790364827693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75165696002177193576551795 112748544003265790364827693)
        ·
          refine ⟨42280704001224671386810385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112748544003265790364827693 42280704001224671386810385)
          ·
            refine ⟨31710528000918503540107789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42280704001224671386810385 31710528000918503540107789)
            ·
              refine ⟨11891448000344438827540421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31710528000918503540107789 11891448000344438827540421)
              ·
                refine ⟨2229646500064582280163829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11891448000344438827540421 2229646500064582280163829)
                ·
                  refine ⟨209029359381054588765359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2229646500064582280163829 209029359381054588765359)
                  ·
                    rfl

theorem cell23_3663749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_3663749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663749 prefixEnd_3663749 := by exact prefixLift 3663749
  have htrace : WordTrace (prefixWord ++ tailWord_3663749) baseStart_3663749 baseEnd_3663749 := by
    simpa [prefixWord, tailWord_3663749, baseEnd_3663749] using wordTrace_append hprefix tailTrace_3663749
  have hstable : (prefixWord ++ tailWord_3663749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663749).length < 2 ^ (prefixWord ++ tailWord_3663749).sum := by decide
  have hdescent : baseEnd_3663749 < baseStart_3663749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663816 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_3663816 : Nat := 118140960795 + 3663816 * 2 ^ 59
def prefixEnd_3663816 : Nat := 4983230072969 + 3 ^ 40 * 3663816 * 2
def baseEnd_3663816 : Nat := 1881298637633342536750423

theorem tailTrace_3663816 : CollatzResearch.WordTrace tailWord_3663816 prefixEnd_3663816 1881298637633342536750423 := by
  unfold tailWord_3663816
  simp only [CollatzResearch.WordTrace]
  refine ⟨66815173847313918400501651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89086898463085224534002201 66815173847313918400501651)
  ·
    refine ⟨100222760770970877600752477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66815173847313918400501651 100222760770970877600752477)
    ·
      refine ⟨37583535289114079100282179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100222760770970877600752477 37583535289114079100282179)
      ·
        refine ⟨56375302933671118650423269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37583535289114079100282179 56375302933671118650423269)
        ·
          refine ⟨10570369300063334746954363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56375302933671118650423269 10570369300063334746954363)
          ·
            refine ⟨15855553950095002120431545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10570369300063334746954363 15855553950095002120431545)
            ·
              refine ⟨11891665462571251590323659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15855553950095002120431545 11891665462571251590323659)
              ·
                refine ⟨17837498193856877385485489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11891665462571251590323659 17837498193856877385485489)
                ·
                  refine ⟨13378123645392658039114117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17837498193856877385485489 13378123645392658039114117)
                  ·
                    refine ⟨2508398183511123382333897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13378123645392658039114117 2508398183511123382333897)
                    ·
                      refine ⟨1881298637633342536750423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2508398183511123382333897 1881298637633342536750423)
                      ·
                        rfl

theorem cell23_3663816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_3663816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663816 prefixEnd_3663816 := by exact prefixLift 3663816
  have htrace : WordTrace (prefixWord ++ tailWord_3663816) baseStart_3663816 baseEnd_3663816 := by
    simpa [prefixWord, tailWord_3663816, baseEnd_3663816] using wordTrace_append hprefix tailTrace_3663816
  have hstable : (prefixWord ++ tailWord_3663816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663816).length < 2 ^ (prefixWord ++ tailWord_3663816).sum := by decide
  have hdescent : baseEnd_3663816 < baseStart_3663816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663843 : List Nat := [1, 1, 1, 6, 1, 2, 3, 3, 1, 4]
def baseStart_3663843 : Nat := 118140960795 + 3663843 * 2 ^ 59
def prefixEnd_3663843 : Nat := 4983230072969 + 3 ^ 40 * 3663843 * 2
def baseEnd_3663843 : Nat := 627104167203671310370933

theorem tailTrace_3663843 : CollatzResearch.WordTrace tailWord_3663843 prefixEnd_3663843 627104167203671310370933 := by
  unfold tailWord_3663843
  simp only [CollatzResearch.WordTrace]
  refine ⟨133631332465530020412236183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89087554977020013608157455 133631332465530020412236183)
  ·
    refine ⟨200446998698295030618354275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133631332465530020412236183 200446998698295030618354275)
    ·
      refine ⟨300670498047442545927531413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200446998698295030618354275 300670498047442545927531413)
      ·
        refine ⟨14093929595973869340353035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 300670498047442545927531413 14093929595973869340353035)
        ·
          refine ⟨21140894393960804010529553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14093929595973869340353035 21140894393960804010529553)
          ·
            refine ⟨15855670795470603007897165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21140894393960804010529553 15855670795470603007897165)
            ·
              refine ⟨5945876548301476127961437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15855670795470603007897165 5945876548301476127961437)
              ·
                refine ⟨2229703705613053547985539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5945876548301476127961437 2229703705613053547985539)
                ·
                  refine ⟨3344555558419580321978309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229703705613053547985539 3344555558419580321978309)
                  ·
                    refine ⟨627104167203671310370933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3344555558419580321978309 627104167203671310370933)
                    ·
                      rfl

theorem cell23_3663843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 3, 1, 4].length) (baseStart_3663843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663843 prefixEnd_3663843 := by exact prefixLift 3663843
  have htrace : WordTrace (prefixWord ++ tailWord_3663843) baseStart_3663843 baseEnd_3663843 := by
    simpa [prefixWord, tailWord_3663843, baseEnd_3663843] using wordTrace_append hprefix tailTrace_3663843
  have hstable : (prefixWord ++ tailWord_3663843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663843).length < 2 ^ (prefixWord ++ tailWord_3663843).sum := by decide
  have hdescent : baseEnd_3663843 < baseStart_3663843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663899 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 4, 4]
def baseStart_3663899 : Nat := 118140960795 + 3663899 * 2 ^ 59
def prefixEnd_3663899 : Nat := 4983230072969 + 3 ^ 40 * 3663899 * 2
def baseEnd_3663899 : Nat := 627113752175888570670847

theorem tailTrace_3663899 : CollatzResearch.WordTrace tailWord_3663899 prefixEnd_3663899 627113752175888570670847 := by
  unfold tailWord_3663899
  simp only [CollatzResearch.WordTrace]
  refine ⟨133633374953327141976274751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89088916635551427984183167 133633374953327141976274751)
  ·
    refine ⟨200450062429990712964412127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133633374953327141976274751 200450062429990712964412127)
    ·
      refine ⟨300675093644986069446618191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200450062429990712964412127 300675093644986069446618191)
      ·
        refine ⟨451012640467479104169927287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300675093644986069446618191 451012640467479104169927287)
        ·
          refine ⟨676518960701218656254890931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451012640467479104169927287 676518960701218656254890931)
          ·
            refine ⟨1014778441051827984382336397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676518960701218656254890931 1014778441051827984382336397)
            ·
              refine ⟨380541915394435494143376149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1014778441051827984382336397 380541915394435494143376149)
              ·
                refine ⟨17837902284114163787970757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 380541915394435494143376149 17837902284114163787970757)
                ·
                  refine ⟨3344606678271405710244517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17837902284114163787970757 3344606678271405710244517)
                  ·
                    refine ⟨627113752175888570670847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3344606678271405710244517 627113752175888570670847)
                    ·
                      rfl

theorem cell23_3663899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 4].length) (baseStart_3663899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663899 prefixEnd_3663899 := by exact prefixLift 3663899
  have htrace : WordTrace (prefixWord ++ tailWord_3663899) baseStart_3663899 baseEnd_3663899 := by
    simpa [prefixWord, tailWord_3663899, baseEnd_3663899] using wordTrace_append hprefix tailTrace_3663899
  have hstable : (prefixWord ++ tailWord_3663899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663899).length < 2 ^ (prefixWord ++ tailWord_3663899).sum := by decide
  have hdescent : baseEnd_3663899 < baseStart_3663899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663926 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3663926 : Nat := 118140960795 + 3663926 * 2 ^ 59
def prefixEnd_3663926 : Nat := 4983230072969 + 3 ^ 40 * 3663926 * 2
def baseEnd_3663926 : Nat := 1881355120505337106374917

theorem tailTrace_3663926 : CollatzResearch.WordTrace tailWord_3663926 prefixEnd_3663926 1881355120505337106374917 := by
  unfold tailWord_3663926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352147482764332849219227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89089573149486217058338421 8352147482764332849219227)
  ·
    refine ⟨12528221224146499273828841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8352147482764332849219227 12528221224146499273828841)
    ·
      refine ⟨9396165918109874455371631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12528221224146499273828841 9396165918109874455371631)
      ·
        refine ⟨14094248877164811683057447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9396165918109874455371631 14094248877164811683057447)
        ·
          refine ⟨21141373315747217524586171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14094248877164811683057447 21141373315747217524586171)
          ·
            refine ⟨31712059973620826286879257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21141373315747217524586171 31712059973620826286879257)
            ·
              refine ⟨23784044980215619715159443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31712059973620826286879257 23784044980215619715159443)
              ·
                refine ⟨35676067470323429572739165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23784044980215619715159443 35676067470323429572739165)
                ·
                  refine ⟨13378525301371286089777187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35676067470323429572739165 13378525301371286089777187)
                  ·
                    refine ⟨20067787952056929134665781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13378525301371286089777187 20067787952056929134665781)
                    ·
                      refine ⟨1881355120505337106374917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20067787952056929134665781 1881355120505337106374917)
                      ·
                        rfl

theorem cell23_3663926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3663926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663926 prefixEnd_3663926 := by exact prefixLift 3663926
  have htrace : WordTrace (prefixWord ++ tailWord_3663926) baseStart_3663926 baseEnd_3663926 := by
    simpa [prefixWord, tailWord_3663926, baseEnd_3663926] using wordTrace_append hprefix tailTrace_3663926
  have hstable : (prefixWord ++ tailWord_3663926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663926).length < 2 ^ (prefixWord ++ tailWord_3663926).sum := by decide
  have hdescent : baseEnd_3663926 < baseStart_3663926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663936 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 4]
def baseStart_3663936 : Nat := 118140960795 + 3663936 * 2 ^ 59
def prefixEnd_3663936 : Nat := 4983230072969 + 3 ^ 40 * 3663936 * 2
def baseEnd_3663936 : Nat := 1881360255311882067249871

theorem tailTrace_3663936 : CollatzResearch.WordTrace tailWord_3663936 prefixEnd_3663936 1881360255311882067249871 := by
  unfold tailWord_3663936
  simp only [CollatzResearch.WordTrace]
  refine ⟨66817362227096548647685831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89089816302795398196914441 66817362227096548647685831)
  ·
    refine ⟨100226043340644822971528747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66817362227096548647685831 100226043340644822971528747)
    ·
      refine ⟨150339065010967234457293121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100226043340644822971528747 150339065010967234457293121)
      ·
        refine ⟨112754298758225425842969841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150339065010967234457293121 112754298758225425842969841)
        ·
          refine ⟨84565724068669069382227381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112754298758225425842969841 84565724068669069382227381)
          ·
            refine ⟨7928036631437725254583817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84565724068669069382227381 7928036631437725254583817)
            ·
              refine ⟨5946027473578293940937863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7928036631437725254583817 5946027473578293940937863)
              ·
                refine ⟨8919041210367440911406795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946027473578293940937863 8919041210367440911406795)
                ·
                  refine ⟨13378561815551161367110193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8919041210367440911406795 13378561815551161367110193)
                  ·
                    refine ⟨10033921361663371025332645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13378561815551161367110193 10033921361663371025332645)
                    ·
                      refine ⟨1881360255311882067249871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10033921361663371025332645 1881360255311882067249871)
                      ·
                        rfl

theorem cell23_3663936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_3663936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663936 prefixEnd_3663936 := by exact prefixLift 3663936
  have htrace : WordTrace (prefixWord ++ tailWord_3663936) baseStart_3663936 baseEnd_3663936 := by
    simpa [prefixWord, tailWord_3663936, baseEnd_3663936] using wordTrace_append hprefix tailTrace_3663936
  have hstable : (prefixWord ++ tailWord_3663936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663936).length < 2 ^ (prefixWord ++ tailWord_3663936).sum := by decide
  have hdescent : baseEnd_3663936 < baseStart_3663936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663957 : List Nat := [1, 3, 2, 2, 1, 4, 2, 3, 1, 2, 2]
def baseStart_3663957 : Nat := 118140960795 + 3663957 * 2 ^ 59
def prefixEnd_3663957 : Nat := 4983230072969 + 3 ^ 40 * 3663957 * 2
def baseEnd_3663957 : Nat := 1881371038405626485087275

theorem tailTrace_3663957 : CollatzResearch.WordTrace tailWord_3663957 prefixEnd_3663957 1881371038405626485087275 := by
  unfold tailWord_3663957
  simp only [CollatzResearch.WordTrace]
  refine ⟨133635490387117017881886125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89090326924744678587924083 133635490387117017881886125)
  ·
    refine ⟨50113308895168881705707297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133635490387117017881886125 50113308895168881705707297)
    ·
      refine ⟨37584981671376661279280473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50113308895168881705707297 37584981671376661279280473)
      ·
        refine ⟨28188736253532495959460355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37584981671376661279280473 28188736253532495959460355)
        ·
          refine ⟨42283104380298743939190533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28188736253532495959460355 42283104380298743939190533)
          ·
            refine ⟨7928082071306014488598225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42283104380298743939190533 7928082071306014488598225)
            ·
              refine ⟨5946061553479510866448669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7928082071306014488598225 5946061553479510866448669)
              ·
                refine ⟨2229773082554816574918251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5946061553479510866448669 2229773082554816574918251)
                ·
                  refine ⟨3344659623832224862377377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229773082554816574918251 3344659623832224862377377)
                  ·
                    refine ⟨2508494717874168646783033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3344659623832224862377377 2508494717874168646783033)
                    ·
                      refine ⟨1881371038405626485087275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2508494717874168646783033 1881371038405626485087275)
                      ·
                        rfl

theorem cell23_3663957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_3663957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663957 prefixEnd_3663957 := by exact prefixLift 3663957
  have htrace : WordTrace (prefixWord ++ tailWord_3663957) baseStart_3663957 baseEnd_3663957 := by
    simpa [prefixWord, tailWord_3663957, baseEnd_3663957] using wordTrace_append hprefix tailTrace_3663957
  have hstable : (prefixWord ++ tailWord_3663957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663957).length < 2 ^ (prefixWord ++ tailWord_3663957).sum := by decide
  have hdescent : baseEnd_3663957 < baseStart_3663957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663960 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 1, 2, 3]
def baseStart_3663960 : Nat := 118140960795 + 3663960 * 2 ^ 59
def prefixEnd_3663960 : Nat := 4983230072969 + 3 ^ 40 * 3663960 * 2
def baseEnd_3663960 : Nat := 1881372578847589973349761

theorem tailTrace_3663960 : CollatzResearch.WordTrace tailWord_3663960 prefixEnd_3663960 1881372578847589973349761 := by
  unfold tailWord_3663960
  simp only [CollatzResearch.WordTrace]
  refine ⟨66817799903053074697122667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89090399870737432929496889 66817799903053074697122667)
  ·
    refine ⟨100226699854579612045684001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66817799903053074697122667 100226699854579612045684001)
    ·
      refine ⟨75170024890934709034263001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100226699854579612045684001 75170024890934709034263001)
      ·
        refine ⟨56377518668201031775697251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75170024890934709034263001 56377518668201031775697251)
        ·
          refine ⟨84566278002301547663545877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56377518668201031775697251 84566278002301547663545877)
          ·
            refine ⟨3964044281357885046728713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84566278002301547663545877 3964044281357885046728713)
            ·
              refine ⟨2973033211018413785046535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3964044281357885046728713 2973033211018413785046535)
              ·
                refine ⟨4459549816527620677569803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973033211018413785046535 4459549816527620677569803)
                ·
                  refine ⟨6689324724791431016354705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459549816527620677569803 6689324724791431016354705)
                  ·
                    refine ⟨5016993543593573262266029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689324724791431016354705 5016993543593573262266029)
                    ·
                      refine ⟨1881372578847589973349761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5016993543593573262266029 1881372578847589973349761)
                      ·
                        rfl

theorem cell23_3663960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_3663960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663960 prefixEnd_3663960 := by exact prefixLift 3663960
  have htrace : WordTrace (prefixWord ++ tailWord_3663960) baseStart_3663960 baseEnd_3663960 := by
    simpa [prefixWord, tailWord_3663960, baseEnd_3663960] using wordTrace_append hprefix tailTrace_3663960
  have hstable : (prefixWord ++ tailWord_3663960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663960).length < 2 ^ (prefixWord ++ tailWord_3663960).sum := by decide
  have hdescent : baseEnd_3663960 < baseStart_3663960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663973 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 3]
def baseStart_3663973 : Nat := 118140960795 + 3663973 * 2 ^ 59
def prefixEnd_3663973 : Nat := 4983230072969 + 3 ^ 40 * 3663973 * 2
def baseEnd_3663973 : Nat := 1881379254096098422487201

theorem tailTrace_3663973 : CollatzResearch.WordTrace tailWord_3663973 prefixEnd_3663973 1881379254096098422487201 := by
  unfold tailWord_3663973
  simp only [CollatzResearch.WordTrace]
  refine ⟨133636073955059052614468573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89090715970039368409645715 133636073955059052614468573)
  ·
    refine ⟨50113527733147144730425715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133636073955059052614468573 50113527733147144730425715)
    ·
      refine ⟨75170291599720717095638573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50113527733147144730425715 75170291599720717095638573)
      ·
        refine ⟨28188859349895268910864465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75170291599720717095638573 28188859349895268910864465)
        ·
          refine ⟨21141644512421451683148349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28188859349895268910864465 21141644512421451683148349)
          ·
            refine ⟨7928116692158044381180631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21141644512421451683148349 7928116692158044381180631)
            ·
              refine ⟨11892175038237066571770947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7928116692158044381180631 11892175038237066571770947)
              ·
                refine ⟨17838262557355599857656421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11892175038237066571770947 17838262557355599857656421)
                ·
                  refine ⟨3344674229504174973310579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17838262557355599857656421 3344674229504174973310579)
                  ·
                    refine ⟨5017011344256262459965869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3344674229504174973310579 5017011344256262459965869)
                    ·
                      refine ⟨1881379254096098422487201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5017011344256262459965869 1881379254096098422487201)
                      ·
                        rfl

theorem cell23_3663973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_3663973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663973 prefixEnd_3663973 := by exact prefixLift 3663973
  have htrace : WordTrace (prefixWord ++ tailWord_3663973) baseStart_3663973 baseEnd_3663973 := by
    simpa [prefixWord, tailWord_3663973, baseEnd_3663973] using wordTrace_append hprefix tailTrace_3663973
  have hstable : (prefixWord ++ tailWord_3663973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663973).length < 2 ^ (prefixWord ++ tailWord_3663973).sum := by decide
  have hdescent : baseEnd_3663973 < baseStart_3663973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663990 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3663990 : Nat := 118140960795 + 3663990 * 2 ^ 59
def prefixEnd_3663990 : Nat := 4983230072969 + 3 ^ 40 * 3663990 * 2
def baseEnd_3663990 : Nat := 1881387983267224855974623

theorem tailTrace_3663990 : CollatzResearch.WordTrace tailWord_3663990 prefixEnd_3663990 1881387983267224855974623 := by
  unfold tailWord_3663990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8352293374749841532364839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89091129330664976345224949 8352293374749841532364839)
  ·
    refine ⟨12528440062124762298547259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8352293374749841532364839 12528440062124762298547259)
    ·
      refine ⟨18792660093187143447820889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12528440062124762298547259 18792660093187143447820889)
      ·
        refine ⟨14094495069890357585865667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18792660093187143447820889 14094495069890357585865667)
        ·
          refine ⟨21141742604835536378798501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14094495069890357585865667 21141742604835536378798501)
          ·
            refine ⟨3964076738406663071024719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21141742604835536378798501 3964076738406663071024719)
            ·
              refine ⟨5946115107609994606537079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964076738406663071024719 5946115107609994606537079)
              ·
                refine ⟨8919172661414991909805619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946115107609994606537079 8919172661414991909805619)
                ·
                  refine ⟨13378758992122487864708429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8919172661414991909805619 13378758992122487864708429)
                  ·
                    refine ⟨5017034622045932949265661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13378758992122487864708429 5017034622045932949265661)
                    ·
                      refine ⟨1881387983267224855974623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5017034622045932949265661 1881387983267224855974623)
                      ·
                        rfl

theorem cell23_3663990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3663990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3663990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3663990 prefixEnd_3663990 := by exact prefixLift 3663990
  have htrace : WordTrace (prefixWord ++ tailWord_3663990) baseStart_3663990 baseEnd_3663990 := by
    simpa [prefixWord, tailWord_3663990, baseEnd_3663990] using wordTrace_append hprefix tailTrace_3663990
  have hstable : (prefixWord ++ tailWord_3663990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663990).length < 2 ^ (prefixWord ++ tailWord_3663990).sum := by decide
  have hdescent : baseEnd_3663990 < baseStart_3663990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664059 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 7]
def baseStart_3664059 : Nat := 118140960795 + 3664059 * 2 ^ 59
def prefixEnd_3664059 : Nat := 4983230072969 + 3 ^ 40 * 3664059 * 2
def baseEnd_3664059 : Nat := 1881423413432385086011805

theorem tailTrace_3664059 : CollatzResearch.WordTrace tailWord_3664059 prefixEnd_3664059 1881423413432385086011805 := by
  unfold tailWord_3664059
  simp only [CollatzResearch.WordTrace]
  refine ⟨133639210632747489302099231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89092807088498326201399487 133639210632747489302099231)
  ·
    refine ⟨200458815949121233953148847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133639210632747489302099231 200458815949121233953148847)
    ·
      refine ⟨300688223923681850929723271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200458815949121233953148847 300688223923681850929723271)
      ·
        refine ⟨451032335885522776394584907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300688223923681850929723271 451032335885522776394584907)
        ·
          refine ⟨676548503828284164591877361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451032335885522776394584907 676548503828284164591877361)
          ·
            refine ⟨507411377871213123443908021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676548503828284164591877361 507411377871213123443908021)
            ·
              refine ⟨47569816675426230322866377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 507411377871213123443908021 47569816675426230322866377)
              ·
                refine ⟨35677362506569672742149783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47569816675426230322866377 35677362506569672742149783)
                ·
                  refine ⟨53516043759854509113224675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35677362506569672742149783 53516043759854509113224675)
                  ·
                    refine ⟨80274065639781763669837013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53516043759854509113224675 80274065639781763669837013)
                    ·
                      refine ⟨1881423413432385086011805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80274065639781763669837013 1881423413432385086011805)
                      ·
                        rfl

theorem cell23_3664059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_3664059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664059 prefixEnd_3664059 := by exact prefixLift 3664059
  have htrace : WordTrace (prefixWord ++ tailWord_3664059) baseStart_3664059 baseEnd_3664059 := by
    simpa [prefixWord, tailWord_3664059, baseEnd_3664059] using wordTrace_append hprefix tailTrace_3664059
  have hstable : (prefixWord ++ tailWord_3664059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664059).length < 2 ^ (prefixWord ++ tailWord_3664059).sum := by decide
  have hdescent : baseEnd_3664059 < baseStart_3664059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664093 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3664093 : Nat := 118140960795 + 3664093 * 2 ^ 59
def prefixEnd_3664093 : Nat := 4983230072969 + 3 ^ 40 * 3664093 * 2
def baseEnd_3664093 : Nat := 1881440871774637952986649

theorem tailTrace_3664093 : CollatzResearch.WordTrace tailWord_3664093 prefixEnd_3664093 1881440871774637952986649 := by
  unfold tailWord_3664093
  simp only [CollatzResearch.WordTrace]
  refine ⟨133640450714624313108836933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89093633809749542072557955 133640450714624313108836933)
  ·
    refine ⟨25057584508992058707906925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133640450714624313108836933 25057584508992058707906925)
    ·
      refine ⟨9396594190872022015465097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25057584508992058707906925 9396594190872022015465097)
      ·
        refine ⟨7047445643154016511598823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9396594190872022015465097 7047445643154016511598823)
        ·
          refine ⟨10571168464731024767398235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7047445643154016511598823 10571168464731024767398235)
          ·
            refine ⟨15856752697096537151097353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10571168464731024767398235 15856752697096537151097353)
            ·
              refine ⟨11892564522822402863323015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15856752697096537151097353 11892564522822402863323015)
              ·
                refine ⟨17838846784233604294984523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11892564522822402863323015 17838846784233604294984523)
                ·
                  refine ⟨26758270176350406442476785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17838846784233604294984523 26758270176350406442476785)
                  ·
                    refine ⟨20068702632262804831857589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26758270176350406442476785 20068702632262804831857589)
                    ·
                      refine ⟨1881440871774637952986649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20068702632262804831857589 1881440871774637952986649)
                      ·
                        rfl

theorem cell23_3664093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3664093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664093 prefixEnd_3664093 := by exact prefixLift 3664093
  have htrace : WordTrace (prefixWord ++ tailWord_3664093) baseStart_3664093 baseEnd_3664093 := by
    simpa [prefixWord, tailWord_3664093, baseEnd_3664093] using wordTrace_append hprefix tailTrace_3664093
  have hstable : (prefixWord ++ tailWord_3664093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664093).length < 2 ^ (prefixWord ++ tailWord_3664093).sum := by decide
  have hdescent : baseEnd_3664093 < baseStart_3664093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664160 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 6]
def baseStart_3664160 : Nat := 118140960795 + 3664160 * 2 ^ 59
def prefixEnd_3664160 : Nat := 4983230072969 + 3 ^ 40 * 3664160 * 2
def baseEnd_3664160 : Nat := 209052808330943243427649

theorem tailTrace_3664160 : CollatzResearch.WordTrace tailWord_3664160 prefixEnd_3664160 209052808330943243427649 := by
  unfold tailWord_3664160
  simp only [CollatzResearch.WordTrace]
  refine ⟨66821447202690791775762967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89095262936921055701017289 66821447202690791775762967)
  ·
    refine ⟨100232170804036187663644451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66821447202690791775762967 100232170804036187663644451)
    ·
      refine ⟨150348256206054281495466677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100232170804036187663644451 150348256206054281495466677)
      ·
        refine ⟨14095149019317588890200001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150348256206054281495466677 14095149019317588890200001)
        ·
          refine ⟨10571361764488191667650001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14095149019317588890200001 10571361764488191667650001)
          ·
            refine ⟨7928521323366143750737501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10571361764488191667650001 7928521323366143750737501)
            ·
              refine ⟨2973195496262303906526563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7928521323366143750737501 2973195496262303906526563)
              ·
                refine ⟨4459793244393455859789845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973195496262303906526563 4459793244393455859789845)
                ·
                  refine ⟨209052808330943243427649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4459793244393455859789845 209052808330943243427649)
                  ·
                    rfl

theorem cell23_3664160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 6].length) (baseStart_3664160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664160 prefixEnd_3664160 := by exact prefixLift 3664160
  have htrace : WordTrace (prefixWord ++ tailWord_3664160) baseStart_3664160 baseEnd_3664160 := by
    simpa [prefixWord, tailWord_3664160, baseEnd_3664160] using wordTrace_append hprefix tailTrace_3664160
  have hstable : (prefixWord ++ tailWord_3664160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664160).length < 2 ^ (prefixWord ++ tailWord_3664160).sum := by decide
  have hdescent : baseEnd_3664160 < baseStart_3664160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664163 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 3, 5, 2]
def baseStart_3664163 : Nat := 118140960795 + 3664163 * 2 ^ 59
def prefixEnd_3664163 : Nat := 4983230072969 + 3 ^ 40 * 3664163 * 2
def baseEnd_3664163 : Nat := 1881476815420452679111327

theorem tailTrace_3664163 : CollatzResearch.WordTrace tailWord_3664163 prefixEnd_3664163 1881476815420452679111327 := by
  unfold tailWord_3664163
  simp only [CollatzResearch.WordTrace]
  refine ⟨133643003824370715063885143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89095335882913810042590095 133643003824370715063885143)
  ·
    refine ⟨200464505736556072595827715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133643003824370715063885143 200464505736556072595827715)
    ·
      refine ⟨300696758604834108893741573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200464505736556072595827715 300696758604834108893741573)
      ·
        refine ⟨56380642238406395417576545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300696758604834108893741573 56380642238406395417576545)
        ·
          refine ⟨42285481678804796563182409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56380642238406395417576545 42285481678804796563182409)
          ·
            refine ⟨31714111259103597422386807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42285481678804796563182409 31714111259103597422386807)
            ·
              refine ⟨47571166888655396133580211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31714111259103597422386807 47571166888655396133580211)
              ·
                refine ⟨71356750332983094200370317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47571166888655396133580211 71356750332983094200370317)
                ·
                  refine ⟨26758781374868660325138869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71356750332983094200370317 26758781374868660325138869)
                  ·
                    refine ⟨2508635753893936905481769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26758781374868660325138869 2508635753893936905481769)
                    ·
                      refine ⟨1881476815420452679111327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2508635753893936905481769 1881476815420452679111327)
                      ·
                        rfl

theorem cell23_3664163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_3664163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664163 prefixEnd_3664163 := by exact prefixLift 3664163
  have htrace : WordTrace (prefixWord ++ tailWord_3664163) baseStart_3664163 baseEnd_3664163 := by
    simpa [prefixWord, tailWord_3664163, baseEnd_3664163] using wordTrace_append hprefix tailTrace_3664163
  have hstable : (prefixWord ++ tailWord_3664163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664163).length < 2 ^ (prefixWord ++ tailWord_3664163).sum := by decide
  have hdescent : baseEnd_3664163 < baseStart_3664163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664190 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3664190 : Nat := 118140960795 + 3664190 * 2 ^ 59
def prefixEnd_3664190 : Nat := 4983230072969 + 3 ^ 40 * 3664190 * 2
def baseEnd_3664190 : Nat := 627163559799374691157901

theorem tailTrace_3664190 : CollatzResearch.WordTrace tailWord_3664190 prefixEnd_3664190 627163559799374691157901 := by
  unfold tailWord_3664190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16705498574409112334389753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89095992396848599116745349 16705498574409112334389753)
  ·
    refine ⟨12529123930806834250792315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16705498574409112334389753 12529123930806834250792315)
    ·
      refine ⟨18793685896210251376188473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12529123930806834250792315 18793685896210251376188473)
      ·
        refine ⟨14095264422157688532141355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18793685896210251376188473 14095264422157688532141355)
        ·
          refine ⟨21142896633236532798212033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14095264422157688532141355 21142896633236532798212033)
          ·
            refine ⟨15857172474927399598659025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21142896633236532798212033 15857172474927399598659025)
            ·
              refine ⟨11892879356195549698994269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15857172474927399598659025 11892879356195549698994269)
              ·
                refine ⟨4459829758573331137122851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11892879356195549698994269 4459829758573331137122851)
                ·
                  refine ⟨6689744637859996705684277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459829758573331137122851 6689744637859996705684277)
                  ·
                    refine ⟨627163559799374691157901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6689744637859996705684277 627163559799374691157901)
                    ·
                      rfl

theorem cell23_3664190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3664190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664190 prefixEnd_3664190 := by exact prefixLift 3664190
  have htrace : WordTrace (prefixWord ++ tailWord_3664190) baseStart_3664190 baseEnd_3664190 := by
    simpa [prefixWord, tailWord_3664190, baseEnd_3664190] using wordTrace_append hprefix tailTrace_3664190
  have hstable : (prefixWord ++ tailWord_3664190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664190).length < 2 ^ (prefixWord ++ tailWord_3664190).sum := by decide
  have hdescent : baseEnd_3664190 < baseStart_3664190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664204 : List Nat := [2, 2, 1, 3, 2, 1, 5, 2, 1, 1, 3]
def baseStart_3664204 : Nat := 118140960795 + 3664204 * 2 ^ 59
def prefixEnd_3664204 : Nat := 4983230072969 + 3 ^ 40 * 3664204 * 2
def baseEnd_3664204 : Nat := 1881497868127287018698639

theorem tailTrace_3664204 : CollatzResearch.WordTrace tailWord_3664204 prefixEnd_3664204 1881497868127287018698639 := by
  unfold tailWord_3664204
  simp only [CollatzResearch.WordTrace]
  refine ⟨66822249608611089533063833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89096332811481452710751777 66822249608611089533063833)
  ·
    refine ⟨50116687206458317149797875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66822249608611089533063833 50116687206458317149797875)
    ·
      refine ⟨75175030809687475724696813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50116687206458317149797875 75175030809687475724696813)
      ·
        refine ⟨28190636553632803396761305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75175030809687475724696813 28190636553632803396761305)
        ·
          refine ⟨21142977415224602547570979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28190636553632803396761305 21142977415224602547570979)
          ·
            refine ⟨31714466122836903821356469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21142977415224602547570979 31714466122836903821356469)
            ·
              refine ⟨2973231199015959733252169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31714466122836903821356469 2973231199015959733252169)
              ·
                refine ⟨2229923399261969799939127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2973231199015959733252169 2229923399261969799939127)
                ·
                  refine ⟨3344885098892954699908691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229923399261969799939127 3344885098892954699908691)
                  ·
                    refine ⟨5017327648339432049863037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3344885098892954699908691 5017327648339432049863037)
                    ·
                      refine ⟨1881497868127287018698639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5017327648339432049863037 1881497868127287018698639)
                      ·
                        rfl

theorem cell23_3664204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_3664204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664204 prefixEnd_3664204 := by exact prefixLift 3664204
  have htrace : WordTrace (prefixWord ++ tailWord_3664204) baseStart_3664204 baseEnd_3664204 := by
    simpa [prefixWord, tailWord_3664204, baseEnd_3664204] using wordTrace_append hprefix tailTrace_3664204
  have hstable : (prefixWord ++ tailWord_3664204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664204).length < 2 ^ (prefixWord ++ tailWord_3664204).sum := by decide
  have hdescent : baseEnd_3664204 < baseStart_3664204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664243 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 3]
def baseStart_3664243 : Nat := 118140960795 + 3664243 * 2 ^ 59
def prefixEnd_3664243 : Nat := 4983230072969 + 3 ^ 40 * 3664243 * 2
def baseEnd_3664243 : Nat := 1881517893872812366110959

theorem tailTrace_3664243 : CollatzResearch.WordTrace tailWord_3664243 prefixEnd_3664243 1881517893872812366110959 := by
  unfold tailWord_3664243
  simp only [CollatzResearch.WordTrace]
  refine ⟨133645921664080888726797383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89097281109387259151198255 133645921664080888726797383)
  ·
    refine ⟨200468882496121333090196075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133645921664080888726797383 200468882496121333090196075)
    ·
      refine ⟨300703323744181999635294113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200468882496121333090196075 300703323744181999635294113)
      ·
        refine ⟨225527492808136499726470585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300703323744181999635294113 225527492808136499726470585)
        ·
          refine ⟨169145619606102374794852939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225527492808136499726470585 169145619606102374794852939)
          ·
            refine ⟨253718429409153562192279409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169145619606102374794852939 253718429409153562192279409)
            ·
              refine ⟨190288822056865171644209557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253718429409153562192279409 190288822056865171644209557)
              ·
                refine ⟨8919788533915554920822323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190288822056865171644209557 8919788533915554920822323)
                ·
                  refine ⟨13379682800873332381233485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8919788533915554920822323 13379682800873332381233485)
                  ·
                    refine ⟨5017381050327499642962557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13379682800873332381233485 5017381050327499642962557)
                    ·
                      refine ⟨1881517893872812366110959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5017381050327499642962557 1881517893872812366110959)
                      ·
                        rfl

theorem cell23_3664243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_3664243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664243 prefixEnd_3664243 := by exact prefixLift 3664243
  have htrace : WordTrace (prefixWord ++ tailWord_3664243) baseStart_3664243 baseEnd_3664243 := by
    simpa [prefixWord, tailWord_3664243, baseEnd_3664243] using wordTrace_append hprefix tailTrace_3664243
  have hstable : (prefixWord ++ tailWord_3664243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664243).length < 2 ^ (prefixWord ++ tailWord_3664243).sum := by decide
  have hdescent : baseEnd_3664243 < baseStart_3664243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664256 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_3664256 : Nat := 118140960795 + 3664256 * 2 ^ 59
def prefixEnd_3664256 : Nat := 4983230072969 + 3 ^ 40 * 3664256 * 2
def baseEnd_3664256 : Nat := 1881524569121320815248399

theorem tailTrace_3664256 : CollatzResearch.WordTrace tailWord_3664256 prefixEnd_3664256 1881524569121320815248399 := by
  unfold tailWord_3664256
  simp only [CollatzResearch.WordTrace]
  refine ⟨66823197906516895973510311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89097597208689194631347081 66823197906516895973510311)
  ·
    refine ⟨100234796859775343960265467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66823197906516895973510311 100234796859775343960265467)
    ·
      refine ⟨150352195289663015940398201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100234796859775343960265467 150352195289663015940398201)
      ·
        refine ⟨112764146467247261955298651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150352195289663015940398201 112764146467247261955298651)
        ·
          refine ⟨169146219700870892932947977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112764146467247261955298651 169146219700870892932947977)
          ·
            refine ⟨126859664775653169699710983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169146219700870892932947977 126859664775653169699710983)
            ·
              refine ⟨190289497163479754549566475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126859664775653169699710983 190289497163479754549566475)
              ·
                refine ⟨285434245745219631824349713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190289497163479754549566475 285434245745219631824349713)
                ·
                  refine ⟨214075684308914723868262285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285434245745219631824349713 214075684308914723868262285)
                  ·
                    refine ⟨80278381615843021450598357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214075684308914723868262285 80278381615843021450598357)
                    ·
                      refine ⟨1881524569121320815248399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80278381615843021450598357 1881524569121320815248399)
                      ·
                        rfl

theorem cell23_3664256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_3664256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664256 prefixEnd_3664256 := by exact prefixLift 3664256
  have htrace : WordTrace (prefixWord ++ tailWord_3664256) baseStart_3664256 baseEnd_3664256 := by
    simpa [prefixWord, tailWord_3664256, baseEnd_3664256] using wordTrace_append hprefix tailTrace_3664256
  have hstable : (prefixWord ++ tailWord_3664256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664256).length < 2 ^ (prefixWord ++ tailWord_3664256).sum := by decide
  have hdescent : baseEnd_3664256 < baseStart_3664256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664287 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 1, 3, 2]
def baseStart_3664287 : Nat := 118140960795 + 3664287 * 2 ^ 59
def prefixEnd_3664287 : Nat := 4983230072969 + 3 ^ 40 * 3664287 * 2
def baseEnd_3664287 : Nat := 1881540487021610193960757

theorem tailTrace_3664287 : CollatzResearch.WordTrace tailWord_3664287 prefixEnd_3664287 1881540487021610193960757 := by
  unfold tailWord_3664287
  simp only [CollatzResearch.WordTrace]
  refine ⟨133647526475921484241399115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89098350983947656160932743 133647526475921484241399115)
  ·
    refine ⟨200471289713882226362098673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133647526475921484241399115 200471289713882226362098673)
    ·
      refine ⟨150353467285411669771574005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200471289713882226362098673 150353467285411669771574005)
      ·
        refine ⟨14095637558007344041085063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150353467285411669771574005 14095637558007344041085063)
        ·
          refine ⟨21143456337011016061627595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14095637558007344041085063 21143456337011016061627595)
          ·
            refine ⟨31715184505516524092441393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21143456337011016061627595 31715184505516524092441393)
            ·
              refine ⟨23786388379137393069331045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31715184505516524092441393 23786388379137393069331045)
              ·
                refine ⟨4459947821088261200499571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23786388379137393069331045 4459947821088261200499571)
                ·
                  refine ⟨6689921731632391800749357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459947821088261200499571 6689921731632391800749357)
                  ·
                    refine ⟨2508720649362146925281009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6689921731632391800749357 2508720649362146925281009)
                    ·
                      refine ⟨1881540487021610193960757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2508720649362146925281009 1881540487021610193960757)
                      ·
                        rfl

theorem cell23_3664287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_3664287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664287 prefixEnd_3664287 := by exact prefixLift 3664287
  have htrace : WordTrace (prefixWord ++ tailWord_3664287) baseStart_3664287 baseEnd_3664287 := by
    simpa [prefixWord, tailWord_3664287, baseEnd_3664287] using wordTrace_append hprefix tailTrace_3664287
  have hstable : (prefixWord ++ tailWord_3664287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664287).length < 2 ^ (prefixWord ++ tailWord_3664287).sum := by decide
  have hdescent : baseEnd_3664287 < baseStart_3664287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664340 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 7]
def baseStart_3664340 : Nat := 118140960795 + 3664340 * 2 ^ 59
def prefixEnd_3664340 : Nat := 4983230072969 + 3 ^ 40 * 3664340 * 2
def baseEnd_3664340 : Nat := 209063077944033165177557

theorem tailTrace_3664340 : CollatzResearch.WordTrace tailWord_3664340 prefixEnd_3664340 209063077944033165177557 := by
  unfold tailWord_3664340
  simp only [CollatzResearch.WordTrace]
  refine ⟨66824729772364737146539237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89099639696486316195385649 66824729772364737146539237)
  ·
    refine ⟨12529636832318388214976107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66824729772364737146539237 12529636832318388214976107)
    ·
      refine ⟨18794455248477582322464161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12529636832318388214976107 18794455248477582322464161)
      ·
        refine ⟨14095841436358186741848121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18794455248477582322464161 14095841436358186741848121)
        ·
          refine ⟨10571881077268640056386091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14095841436358186741848121 10571881077268640056386091)
          ·
            refine ⟨15857821615902960084579137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10571881077268640056386091 15857821615902960084579137)
            ·
              refine ⟨11893366211927220063434353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15857821615902960084579137 11893366211927220063434353)
              ·
                refine ⟨8920024658945415047575765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11893366211927220063434353 8920024658945415047575765)
                ·
                  refine ⟨209063077944033165177557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8920024658945415047575765 209063077944033165177557)
                  ·
                    rfl

theorem cell23_3664340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_3664340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664340 prefixEnd_3664340 := by exact prefixLift 3664340
  have htrace : WordTrace (prefixWord ++ tailWord_3664340) baseStart_3664340 baseEnd_3664340 := by
    simpa [prefixWord, tailWord_3664340, baseEnd_3664340] using wordTrace_append hprefix tailTrace_3664340
  have hstable : (prefixWord ++ tailWord_3664340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664340).length < 2 ^ (prefixWord ++ tailWord_3664340).sum := by decide
  have hdescent : baseEnd_3664340 < baseStart_3664340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664353 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 1, 7]
def baseStart_3664353 : Nat := 118140960795 + 3664353 * 2 ^ 59
def prefixEnd_3664353 : Nat := 4983230072969 + 3 ^ 40 * 3664353 * 2
def baseEnd_3664353 : Nat := 627191458914935645245151

theorem tailTrace_3664353 : CollatzResearch.WordTrace tailWord_3664353 prefixEnd_3664353 627191458914935645245151 := by
  unfold tailWord_3664353
  simp only [CollatzResearch.WordTrace]
  refine ⟨133649933693682377513301713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89099955795788251675534475 133649933693682377513301713)
  ·
    refine ⟨100237450270261783134976285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133649933693682377513301713 100237450270261783134976285)
    ·
      refine ⟨37589043851348168675616107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100237450270261783134976285 37589043851348168675616107)
      ·
        refine ⟨56383565777022253013424161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37589043851348168675616107 56383565777022253013424161)
        ·
          refine ⟨42287674332766689760068121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56383565777022253013424161 42287674332766689760068121)
          ·
            refine ⟨31715755749575017320051091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42287674332766689760068121 31715755749575017320051091)
            ·
              refine ⟨47573633624362525980076637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31715755749575017320051091 47573633624362525980076637)
              ·
                refine ⟨17840112609135947242528739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47573633624362525980076637 17840112609135947242528739)
                ·
                  refine ⟨26760168913703920863793109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17840112609135947242528739 26760168913703920863793109)
                  ·
                    refine ⟨627191458914935645245151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26760168913703920863793109 627191458914935645245151)
                    ·
                      rfl

theorem cell23_3664353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_3664353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664353 prefixEnd_3664353 := by exact prefixLift 3664353
  have htrace : WordTrace (prefixWord ++ tailWord_3664353) baseStart_3664353 baseEnd_3664353 := by
    simpa [prefixWord, tailWord_3664353, baseEnd_3664353] using wordTrace_append hprefix tailTrace_3664353
  have hstable : (prefixWord ++ tailWord_3664353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664353).length < 2 ^ (prefixWord ++ tailWord_3664353).sum := by decide
  have hdescent : baseEnd_3664353 < baseStart_3664353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664354 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3664354 : Nat := 118140960795 + 3664354 * 2 ^ 59
def prefixEnd_3664354 : Nat := 4983230072969 + 3 ^ 40 * 3664354 * 2
def baseEnd_3664354 : Nat := 1881574890225461431822949

theorem tailTrace_3664354 : CollatzResearch.WordTrace tailWord_3664354 prefixEnd_3664354 1881574890225461431822949 := by
  unfold tailWord_3664354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33412492541669688671022029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89099980111119169789392077 33412492541669688671022029)
  ·
    refine ⟨12529684703126133251633261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33412492541669688671022029 12529684703126133251633261)
    ·
      refine ⟨4698631763672299969362473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12529684703126133251633261 4698631763672299969362473)
      ·
        refine ⟨3523973822754224977021855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4698631763672299969362473 3523973822754224977021855)
        ·
          refine ⟨5285960734131337465532783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523973822754224977021855 5285960734131337465532783)
          ·
            refine ⟨7928941101197006198299175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285960734131337465532783 7928941101197006198299175)
            ·
              refine ⟨11893411651795509297448763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7928941101197006198299175 11893411651795509297448763)
              ·
                refine ⟨17840117477693263946173145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11893411651795509297448763 17840117477693263946173145)
                ·
                  refine ⟨13380088108269947959629859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17840117477693263946173145 13380088108269947959629859)
                  ·
                    refine ⟨20070132162404921939444789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13380088108269947959629859 20070132162404921939444789)
                    ·
                      refine ⟨1881574890225461431822949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20070132162404921939444789 1881574890225461431822949)
                      ·
                        rfl

theorem cell23_3664354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3664354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664354 prefixEnd_3664354 := by exact prefixLift 3664354
  have htrace : WordTrace (prefixWord ++ tailWord_3664354) baseStart_3664354 baseEnd_3664354 := by
    simpa [prefixWord, tailWord_3664354, baseEnd_3664354] using wordTrace_append hprefix tailTrace_3664354
  have hstable : (prefixWord ++ tailWord_3664354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664354).length < 2 ^ (prefixWord ++ tailWord_3664354).sum := by decide
  have hdescent : baseEnd_3664354 < baseStart_3664354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664363 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 5]
def baseStart_3664363 : Nat := 118140960795 + 3664363 * 2 ^ 59
def prefixEnd_3664363 : Nat := 4983230072969 + 3 ^ 40 * 3664363 * 2
def baseEnd_3664363 : Nat := 1881579511551351896610407

theorem tailTrace_3664363 : CollatzResearch.WordTrace tailWord_3664363 prefixEnd_3664363 1881579511551351896610407 := by
  unfold tailWord_3664363
  simp only [CollatzResearch.WordTrace]
  refine ⟨133650298423646149221165743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89100198949097432814110495 133650298423646149221165743)
  ·
    refine ⟨200475447635469223831748615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133650298423646149221165743 200475447635469223831748615)
    ·
      refine ⟨300713171453203835747622923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200475447635469223831748615 300713171453203835747622923)
      ·
        refine ⟨451069757179805753621434385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300713171453203835747622923 451069757179805753621434385)
        ·
          refine ⟨338302317884854315216075789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451069757179805753621434385 338302317884854315216075789)
          ·
            refine ⟨126863369206820368206028421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338302317884854315216075789 126863369206820368206028421)
            ·
              refine ⟨23786881726278819038630329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126863369206820368206028421 23786881726278819038630329)
              ·
                refine ⟨17840161294709114278972747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23786881726278819038630329 17840161294709114278972747)
                ·
                  refine ⟨26760241942063671418459121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17840161294709114278972747 26760241942063671418459121)
                  ·
                    refine ⟨20070181456547753563844341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26760241942063671418459121 20070181456547753563844341)
                    ·
                      refine ⟨1881579511551351896610407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20070181456547753563844341 1881579511551351896610407)
                      ·
                        rfl

theorem cell23_3664363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_3664363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664363 prefixEnd_3664363 := by exact prefixLift 3664363
  have htrace : WordTrace (prefixWord ++ tailWord_3664363) baseStart_3664363 baseEnd_3664363 := by
    simpa [prefixWord, tailWord_3664363, baseEnd_3664363] using wordTrace_append hprefix tailTrace_3664363
  have hstable : (prefixWord ++ tailWord_3664363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664363).length < 2 ^ (prefixWord ++ tailWord_3664363).sum := by decide
  have hdescent : baseEnd_3664363 < baseStart_3664363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664374 : List Nat := [5, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_3664374 : Nat := 118140960795 + 3664374 * 2 ^ 59
def prefixEnd_3664374 : Nat := 4983230072969 + 3 ^ 40 * 3664374 * 2
def baseEnd_3664374 : Nat := 209065017759839039285873

theorem tailTrace_3664374 : CollatzResearch.WordTrace tailWord_3664374 prefixEnd_3664374 209065017759839039285873 := by
  unfold tailWord_3664374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8353168726662893631238511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89100466417737532066544117 8353168726662893631238511)
  ·
    refine ⟨12529753089994340446857767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8353168726662893631238511 12529753089994340446857767)
    ·
      refine ⟨18794629634991510670286651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12529753089994340446857767 18794629634991510670286651)
      ·
        refine ⟨28191944452487266005429977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18794629634991510670286651 28191944452487266005429977)
        ·
          refine ⟨21143958339365449504072483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28191944452487266005429977 21143958339365449504072483)
          ·
            refine ⟨31715937509048174256108725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21143958339365449504072483 31715937509048174256108725)
            ·
              refine ⟨2973369141473266336510193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31715937509048174256108725 2973369141473266336510193)
              ·
                refine ⟨2230026856104949752382645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2973369141473266336510193 2230026856104949752382645)
                ·
                  refine ⟨209065017759839039285873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2230026856104949752382645 209065017759839039285873)
                  ·
                    rfl

theorem cell23_3664374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_3664374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664374 prefixEnd_3664374 := by exact prefixLift 3664374
  have htrace : WordTrace (prefixWord ++ tailWord_3664374) baseStart_3664374 baseEnd_3664374 := by
    simpa [prefixWord, tailWord_3664374, baseEnd_3664374] using wordTrace_append hprefix tailTrace_3664374
  have hstable : (prefixWord ++ tailWord_3664374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664374).length < 2 ^ (prefixWord ++ tailWord_3664374).sum := by decide
  have hdescent : baseEnd_3664374 < baseStart_3664374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664404 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3664404 : Nat := 118140960795 + 3664404 * 2 ^ 59
def prefixEnd_3664404 : Nat := 4983230072969 + 3 ^ 40 * 3664404 * 2
def baseEnd_3664404 : Nat := 627200188086062078732573

theorem tailTrace_3664404 : CollatzResearch.WordTrace tailWord_3664404 prefixEnd_3664404 627200188086062078732573 := by
  unfold tailWord_3664404
  simp only [CollatzResearch.WordTrace]
  refine ⟨66825896908248806611704133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89101195877665075482272177 66825896908248806611704133)
  ·
    refine ⟨12529855670296651239694525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66825896908248806611704133 12529855670296651239694525)
    ·
      refine ⟨4698695876361244214885447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12529855670296651239694525 4698695876361244214885447)
      ·
        refine ⟨7048043814541866322328171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698695876361244214885447 7048043814541866322328171)
        ·
          refine ⟨10572065721812799483492257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048043814541866322328171 10572065721812799483492257)
          ·
            refine ⟨7929049291359599612619193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10572065721812799483492257 7929049291359599612619193)
            ·
              refine ⟨5946786968519699709464395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7929049291359599612619193 5946786968519699709464395)
              ·
                refine ⟨8920180452779549564196593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946786968519699709464395 8920180452779549564196593)
                ·
                  refine ⟨6690135339584662173147445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8920180452779549564196593 6690135339584662173147445)
                  ·
                    refine ⟨627200188086062078732573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6690135339584662173147445 627200188086062078732573)
                    ·
                      rfl

theorem cell23_3664404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3664404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664404 prefixEnd_3664404 := by exact prefixLift 3664404
  have htrace : WordTrace (prefixWord ++ tailWord_3664404) baseStart_3664404 baseEnd_3664404 := by
    simpa [prefixWord, tailWord_3664404, baseEnd_3664404] using wordTrace_append hprefix tailTrace_3664404
  have hstable : (prefixWord ++ tailWord_3664404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664404).length < 2 ^ (prefixWord ++ tailWord_3664404).sum := by decide
  have hdescent : baseEnd_3664404 < baseStart_3664404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664410 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_3664410 : Nat := 118140960795 + 3664410 * 2 ^ 59
def prefixEnd_3664410 : Nat := 4983230072969 + 3 ^ 40 * 3664410 * 2
def baseEnd_3664410 : Nat := 1881603645142113212722691

theorem tailTrace_3664410 : CollatzResearch.WordTrace tailWord_3664410 prefixEnd_3664410 1881603645142113212722691 := by
  unfold tailWord_3664410
  simp only [CollatzResearch.WordTrace]
  refine ⟨33413003163618969062031671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89101341769650584165417789 33413003163618969062031671)
  ·
    refine ⟨50119504745428453593047507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33413003163618969062031671 50119504745428453593047507)
    ·
      refine ⟨75179257118142680389571261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50119504745428453593047507 75179257118142680389571261)
      ·
        refine ⟨28192221419303505146089223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75179257118142680389571261 28192221419303505146089223)
        ·
          refine ⟨42288332128955257719133835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28192221419303505146089223 42288332128955257719133835)
          ·
            refine ⟨63432498193432886578700753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42288332128955257719133835 63432498193432886578700753)
            ·
              refine ⟨47574373645074664934025565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63432498193432886578700753 47574373645074664934025565)
              ·
                refine ⟨17840390116902999350259587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47574373645074664934025565 17840390116902999350259587)
                ·
                  refine ⟨26760585175354499025389381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17840390116902999350259587 26760585175354499025389381)
                  ·
                    refine ⟨5017609720378968567260509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26760585175354499025389381 5017609720378968567260509)
                    ·
                      refine ⟨1881603645142113212722691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5017609720378968567260509 1881603645142113212722691)
                      ·
                        rfl

theorem cell23_3664410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_3664410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664410 prefixEnd_3664410 := by exact prefixLift 3664410
  have htrace : WordTrace (prefixWord ++ tailWord_3664410) baseStart_3664410 baseEnd_3664410 := by
    simpa [prefixWord, tailWord_3664410, baseEnd_3664410] using wordTrace_append hprefix tailTrace_3664410
  have hstable : (prefixWord ++ tailWord_3664410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664410).length < 2 ^ (prefixWord ++ tailWord_3664410).sum := by decide
  have hdescent : baseEnd_3664410 < baseStart_3664410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664460 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_3664460 : Nat := 118140960795 + 3664460 * 2 ^ 59
def prefixEnd_3664460 : Nat := 4983230072969 + 3 ^ 40 * 3664460 * 2
def baseEnd_3664460 : Nat := 627209773058279339032487

theorem tailTrace_3664460 : CollatzResearch.WordTrace tailWord_3664460 prefixEnd_3664460 627209773058279339032487 := by
  unfold tailWord_3664460
  simp only [CollatzResearch.WordTrace]
  refine ⟨66826918152147367393723417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89102557536196489858297889 66826918152147367393723417)
  ·
    refine ⟨50120188614110525545292563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66826918152147367393723417 50120188614110525545292563)
    ·
      refine ⟨75180282921165788317938845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50120188614110525545292563 75180282921165788317938845)
      ·
        refine ⟨28192606095437170619227067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75180282921165788317938845 28192606095437170619227067)
        ·
          refine ⟨42288909143155755928840601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28192606095437170619227067 42288909143155755928840601)
          ·
            refine ⟨31716681857366816946630451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42288909143155755928840601 31716681857366816946630451)
            ·
              refine ⟨47575022786050225419945677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31716681857366816946630451 47575022786050225419945677)
              ·
                refine ⟨17840633544768834532479629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47575022786050225419945677 17840633544768834532479629)
                ·
                  refine ⟨6690237579288312949679861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17840633544768834532479629 6690237579288312949679861)
                  ·
                    refine ⟨627209773058279339032487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6690237579288312949679861 627209773058279339032487)
                    ·
                      rfl

theorem cell23_3664460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_3664460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664460 prefixEnd_3664460 := by exact prefixLift 3664460
  have htrace : WordTrace (prefixWord ++ tailWord_3664460) baseStart_3664460 baseEnd_3664460 := by
    simpa [prefixWord, tailWord_3664460, baseEnd_3664460] using wordTrace_append hprefix tailTrace_3664460
  have hstable : (prefixWord ++ tailWord_3664460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664460).length < 2 ^ (prefixWord ++ tailWord_3664460).sum := by decide
  have hdescent : baseEnd_3664460 < baseStart_3664460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664461 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3664461 : Nat := 118140960795 + 3664461 * 2 ^ 59
def prefixEnd_3664461 : Nat := 4983230072969 + 3 ^ 40 * 3664461 * 2
def baseEnd_3664461 : Nat := 1881629832655492513184957

theorem tailTrace_3664461 : CollatzResearch.WordTrace tailWord_3664461 prefixEnd_3664461 1881629832655492513184957 := by
  unfold tailWord_3664461
  simp only [CollatzResearch.WordTrace]
  refine ⟨133653872777291111958233237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89102581851527407972155491 133653872777291111958233237)
  ·
    refine ⟨6265025286435520873042183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133653872777291111958233237 6265025286435520873042183)
    ·
      refine ⟨9397537929653281309563275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6265025286435520873042183 9397537929653281309563275)
      ·
        refine ⟨14096306894479921964344913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9397537929653281309563275 14096306894479921964344913)
        ·
          refine ⟨10572230170859941473258685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14096306894479921964344913 10572230170859941473258685)
          ·
            refine ⟨3964586314072478052472007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10572230170859941473258685 3964586314072478052472007)
            ·
              refine ⟨5946879471108717078708011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964586314072478052472007 5946879471108717078708011)
              ·
                refine ⟨8920319206663075618062017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946879471108717078708011 8920319206663075618062017)
                ·
                  refine ⟨6690239404997306713546513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8920319206663075618062017 6690239404997306713546513)
                  ·
                    refine ⟨5017679553747980035159885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6690239404997306713546513 5017679553747980035159885)
                    ·
                      refine ⟨1881629832655492513184957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5017679553747980035159885 1881629832655492513184957)
                      ·
                        rfl

theorem cell23_3664461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3664461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664461 prefixEnd_3664461 := by exact prefixLift 3664461
  have htrace : WordTrace (prefixWord ++ tailWord_3664461) baseStart_3664461 baseEnd_3664461 := by
    simpa [prefixWord, tailWord_3664461, baseEnd_3664461] using wordTrace_append hprefix tailTrace_3664461
  have hstable : (prefixWord ++ tailWord_3664461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664461).length < 2 ^ (prefixWord ++ tailWord_3664461).sum := by decide
  have hdescent : baseEnd_3664461 < baseStart_3664461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664558 : List Nat := [4, 1, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3664558 : Nat := 118140960795 + 3664558 * 2 ^ 59
def prefixEnd_3664558 : Nat := 4983230072969 + 3 ^ 40 * 3664558 * 2
def baseEnd_3664558 : Nat := 627226546759659544557337

theorem tailTrace_3664558 : CollatzResearch.WordTrace tailWord_3664558 prefixEnd_3664558 627226546759659544557337 := by
  unfold tailWord_3664558
  simp only [CollatzResearch.WordTrace]
  refine ⟨16707176332242462190564291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89104940438626465016342885 16707176332242462190564291)
  ·
    refine ⟨25060764498363693285846437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16707176332242462190564291 25060764498363693285846437)
    ·
      refine ⟨4698893343443192491096207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25060764498363693285846437 4698893343443192491096207)
      ·
        refine ⟨7048340015164788736644311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698893343443192491096207 7048340015164788736644311)
        ·
          refine ⟨10572510022747183104966467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048340015164788736644311 10572510022747183104966467)
          ·
            refine ⟨15858765034120774657449701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10572510022747183104966467 15858765034120774657449701)
            ·
              refine ⟨2973518443897645248271819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15858765034120774657449701 2973518443897645248271819)
              ·
                refine ⟨4460277665846467872407729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973518443897645248271819 4460277665846467872407729)
                ·
                  refine ⟨3345208249384850904305797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4460277665846467872407729 3345208249384850904305797)
                  ·
                    refine ⟨627226546759659544557337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345208249384850904305797 627226546759659544557337)
                    ·
                      rfl

theorem cell23_3664558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3664558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664558 prefixEnd_3664558 := by exact prefixLift 3664558
  have htrace : WordTrace (prefixWord ++ tailWord_3664558) baseStart_3664558 baseEnd_3664558 := by
    simpa [prefixWord, tailWord_3664558, baseEnd_3664558] using wordTrace_append hprefix tailTrace_3664558
  have hstable : (prefixWord ++ tailWord_3664558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664558).length < 2 ^ (prefixWord ++ tailWord_3664558).sum := by decide
  have hdescent : baseEnd_3664558 < baseStart_3664558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664604 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3664604 : Nat := 118140960795 + 3664604 * 2 ^ 59
def prefixEnd_3664604 : Nat := 4983230072969 + 3 ^ 40 * 3664604 * 2
def baseEnd_3664604 : Nat := 1881703260389085453696799

theorem tailTrace_3664604 : CollatzResearch.WordTrace tailWord_3664604 prefixEnd_3664604 1881703260389085453696799 := by
  unfold tailWord_3664604
  simp only [CollatzResearch.WordTrace]
  refine ⟨66829544207886523690344433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89106058943848698253792577 66829544207886523690344433)
  ·
    refine ⟨50122158155914892767758325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66829544207886523690344433 50122158155914892767758325)
    ·
      refine ⟨4698952327117021196977343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50122158155914892767758325 4698952327117021196977343)
      ·
        refine ⟨7048428490675531795466015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698952327117021196977343 7048428490675531795466015)
        ·
          refine ⟨10572642736013297693199023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048428490675531795466015 10572642736013297693199023)
          ·
            refine ⟨15858964104019946539798535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10572642736013297693199023 15858964104019946539798535)
            ·
              refine ⟨23788446156029919809697803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15858964104019946539798535 23788446156029919809697803)
              ·
                refine ⟨35682669234044879714546705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23788446156029919809697803 35682669234044879714546705)
                ·
                  refine ⟨26762001925533659785910029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35682669234044879714546705 26762001925533659785910029)
                  ·
                    refine ⟨10035750722075122419716261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26762001925533659785910029 10035750722075122419716261)
                    ·
                      refine ⟨1881703260389085453696799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10035750722075122419716261 1881703260389085453696799)
                      ·
                        rfl

theorem cell23_3664604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3664604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664604 prefixEnd_3664604 := by exact prefixLift 3664604
  have htrace : WordTrace (prefixWord ++ tailWord_3664604) baseStart_3664604 baseEnd_3664604 := by
    simpa [prefixWord, tailWord_3664604, baseEnd_3664604] using wordTrace_append hprefix tailTrace_3664604
  have hstable : (prefixWord ++ tailWord_3664604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664604).length < 2 ^ (prefixWord ++ tailWord_3664604).sum := by decide
  have hdescent : baseEnd_3664604 < baseStart_3664604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664607 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 3]
def baseStart_3664607 : Nat := 118140960795 + 3664607 * 2 ^ 59
def prefixEnd_3664607 : Nat := 4983230072969 + 3 ^ 40 * 3664607 * 2
def baseEnd_3664607 : Nat := 1881704800831048941959285

theorem tailTrace_3664607 : CollatzResearch.WordTrace tailWord_3664607 prefixEnd_3664607 1881704800831048941959285 := by
  unfold tailWord_3664607
  simp only [CollatzResearch.WordTrace]
  refine ⟨133659197834762178893048075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89106131889841452595365383 133659197834762178893048075)
  ·
    refine ⟨200488796752143268339572113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133659197834762178893048075 200488796752143268339572113)
    ·
      refine ⟨150366597564107451254679085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200488796752143268339572113 150366597564107451254679085)
      ·
        refine ⟨56387474086540294220504657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150366597564107451254679085 56387474086540294220504657)
        ·
          refine ⟨42290605564905220665378493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56387474086540294220504657 42290605564905220665378493)
          ·
            refine ⟨15858977086839457749516935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42290605564905220665378493 15858977086839457749516935)
            ·
              refine ⟨23788465630259186624275403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15858977086839457749516935 23788465630259186624275403)
              ·
                refine ⟨35682698445388779936413105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23788465630259186624275403 35682698445388779936413105)
                ·
                  refine ⟨26762023834041584952309829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35682698445388779936413105 26762023834041584952309829)
                  ·
                    refine ⟨5017879468882797178558093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26762023834041584952309829 5017879468882797178558093)
                    ·
                      refine ⟨1881704800831048941959285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5017879468882797178558093 1881704800831048941959285)
                      ·
                        rfl

theorem cell23_3664607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_3664607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664607 prefixEnd_3664607 := by exact prefixLift 3664607
  have htrace : WordTrace (prefixWord ++ tailWord_3664607) baseStart_3664607 baseEnd_3664607 := by
    simpa [prefixWord, tailWord_3664607, baseEnd_3664607] using wordTrace_append hprefix tailTrace_3664607
  have hstable : (prefixWord ++ tailWord_3664607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664607).length < 2 ^ (prefixWord ++ tailWord_3664607).sum := by decide
  have hdescent : baseEnd_3664607 < baseStart_3664607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664621 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_3664621 : Nat := 118140960795 + 3664621 * 2 ^ 59
def prefixEnd_3664621 : Nat := 4983230072969 + 3 ^ 40 * 3664621 * 2
def baseEnd_3664621 : Nat := 1881711989560211887184221

theorem tailTrace_3664621 : CollatzResearch.WordTrace tailWord_3664621 prefixEnd_3664621 1881711989560211887184221 := by
  unfold tailWord_3664621
  simp only [CollatzResearch.WordTrace]
  refine ⟨133659708456711459284057717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89106472304474306189371811 133659708456711459284057717)
  ·
    refine ⟨12530597667816699307880411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133659708456711459284057717 12530597667816699307880411)
    ·
      refine ⟨18795896501725048961820617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12530597667816699307880411 18795896501725048961820617)
      ·
        refine ⟨14096922376293786721365463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18795896501725048961820617 14096922376293786721365463)
        ·
          refine ⟨21145383564440680082048195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14096922376293786721365463 21145383564440680082048195)
          ·
            refine ⟨31718075346661020123072293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21145383564440680082048195 31718075346661020123072293)
            ·
              refine ⟨5947139127498941273076055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31718075346661020123072293 5947139127498941273076055)
              ·
                refine ⟨8920708691248411909614083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947139127498941273076055 8920708691248411909614083)
                ·
                  refine ⟨13381063036872617864421125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8920708691248411909614083 13381063036872617864421125)
                  ·
                    refine ⟨2508949319413615849578961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13381063036872617864421125 2508949319413615849578961)
                    ·
                      refine ⟨1881711989560211887184221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2508949319413615849578961 1881711989560211887184221)
                      ·
                        rfl

theorem cell23_3664621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_3664621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664621 prefixEnd_3664621 := by exact prefixLift 3664621
  have htrace : WordTrace (prefixWord ++ tailWord_3664621) baseStart_3664621 baseEnd_3664621 := by
    simpa [prefixWord, tailWord_3664621, baseEnd_3664621] using wordTrace_append hprefix tailTrace_3664621
  have hstable : (prefixWord ++ tailWord_3664621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664621).length < 2 ^ (prefixWord ++ tailWord_3664621).sum := by decide
  have hdescent : baseEnd_3664621 < baseStart_3664621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664637 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_3664637 : Nat := 118140960795 + 3664637 * 2 ^ 59
def prefixEnd_3664637 : Nat := 4983230072969 + 3 ^ 40 * 3664637 * 2
def baseEnd_3664637 : Nat := 1881720205250683824584147

theorem tailTrace_3664637 : CollatzResearch.WordTrace tailWord_3664637 prefixEnd_3664637 1881720205250683824584147 := by
  unfold tailWord_3664637
  simp only [CollatzResearch.WordTrace]
  refine ⟨133660292024653494016640165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89106861349768996011093443 133660292024653494016640165)
  ·
    refine ⟨25061304754622530128120031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133660292024653494016640165 25061304754622530128120031)
    ·
      refine ⟨37591957131933795192180047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25061304754622530128120031 37591957131933795192180047)
      ·
        refine ⟨56387935697900692788270071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37591957131933795192180047 56387935697900692788270071)
        ·
          refine ⟨84581903546851039182405107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56387935697900692788270071 84581903546851039182405107)
          ·
            refine ⟨126872855320276558773607661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84581903546851039182405107 126872855320276558773607661)
            ·
              refine ⟨47577320745103709540102873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126872855320276558773607661 47577320745103709540102873)
              ·
                refine ⟨35682990558827782155077155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47577320745103709540102873 35682990558827782155077155)
                ·
                  refine ⟨53524485838241673232615733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35682990558827782155077155 53524485838241673232615733)
                  ·
                    refine ⟨5017920547335156865557725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53524485838241673232615733 5017920547335156865557725)
                    ·
                      refine ⟨1881720205250683824584147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5017920547335156865557725 1881720205250683824584147)
                      ·
                        rfl

theorem cell23_3664637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_3664637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664637 prefixEnd_3664637 := by exact prefixLift 3664637
  have htrace : WordTrace (prefixWord ++ tailWord_3664637) baseStart_3664637 baseEnd_3664637 := by
    simpa [prefixWord, tailWord_3664637, baseEnd_3664637] using wordTrace_append hprefix tailTrace_3664637
  have hstable : (prefixWord ++ tailWord_3664637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664637).length < 2 ^ (prefixWord ++ tailWord_3664637).sum := by decide
  have hdescent : baseEnd_3664637 < baseStart_3664637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664657 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 2, 5]
def baseStart_3664657 : Nat := 118140960795 + 3664657 * 2 ^ 59
def prefixEnd_3664657 : Nat := 4983230072969 + 3 ^ 40 * 3664657 * 2
def baseEnd_3664657 : Nat := 627243491621257915444685

theorem tailTrace_3664657 : CollatzResearch.WordTrace tailWord_3664657 prefixEnd_3664657 627243491621257915444685 := by
  unfold tailWord_3664657
  simp only [CollatzResearch.WordTrace]
  refine ⟨133661021484581037432368225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89107347656387358288245483 133661021484581037432368225)
  ·
    refine ⟨100245766113435778074276169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133661021484581037432368225 100245766113435778074276169)
    ·
      refine ⟨75184324585076833555707127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100245766113435778074276169 75184324585076833555707127)
      ·
        refine ⟨112776486877615250333560691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75184324585076833555707127 112776486877615250333560691)
        ·
          refine ⟨169164730316422875500341037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112776486877615250333560691 169164730316422875500341037)
          ·
            refine ⟨63436773868658578312627889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169164730316422875500341037 63436773868658578312627889)
            ·
              refine ⟨47577580401493933734470917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63436773868658578312627889 47577580401493933734470917)
              ·
                refine ⟨8920796325280112575213297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47577580401493933734470917 8920796325280112575213297)
                ·
                  refine ⟨6690597243960084431409973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8920796325280112575213297 6690597243960084431409973)
                  ·
                    refine ⟨627243491621257915444685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6690597243960084431409973 627243491621257915444685)
                    ·
                      rfl

theorem cell23_3664657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_3664657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664657 prefixEnd_3664657 := by exact prefixLift 3664657
  have htrace : WordTrace (prefixWord ++ tailWord_3664657) baseStart_3664657 baseEnd_3664657 := by
    simpa [prefixWord, tailWord_3664657, baseEnd_3664657] using wordTrace_append hprefix tailTrace_3664657
  have hstable : (prefixWord ++ tailWord_3664657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664657).length < 2 ^ (prefixWord ++ tailWord_3664657).sum := by decide
  have hdescent : baseEnd_3664657 < baseStart_3664657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664677 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3664677 : Nat := 118140960795 + 3664677 * 2 ^ 59
def prefixEnd_3664677 : Nat := 4983230072969 + 3 ^ 40 * 3664677 * 2
def baseEnd_3664677 : Nat := 1881740744476863668083963

theorem tailTrace_3664677 : CollatzResearch.WordTrace tailWord_3664677 prefixEnd_3664677 1881740744476863668083963 := by
  unfold tailWord_3664677
  simp only [CollatzResearch.WordTrace]
  refine ⟨133661750944508580848096285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89107833963005720565397523 133661750944508580848096285)
  ·
    refine ⟨50123156604190717818036107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133661750944508580848096285 50123156604190717818036107)
    ·
      refine ⟨75184734906286076727054161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50123156604190717818036107 75184734906286076727054161)
      ·
        refine ⟨56388551179714557545290621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75184734906286076727054161 56388551179714557545290621)
        ·
          refine ⟨21145706692392959079483983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56388551179714557545290621 21145706692392959079483983)
          ·
            refine ⟨31718560038589438619225975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21145706692392959079483983 31718560038589438619225975)
            ·
              refine ⟨47577840057884157928838963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31718560038589438619225975 47577840057884157928838963)
              ·
                refine ⟨71366760086826236893258445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47577840057884157928838963 71366760086826236893258445)
                ·
                  refine ⟨26762535032559838834971917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71366760086826236893258445 26762535032559838834971917)
                  ·
                    refine ⟨10035950637209939563114469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26762535032559838834971917 10035950637209939563114469)
                    ·
                      refine ⟨1881740744476863668083963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10035950637209939563114469 1881740744476863668083963)
                      ·
                        rfl

theorem cell23_3664677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3664677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664677 prefixEnd_3664677 := by exact prefixLift 3664677
  have htrace : WordTrace (prefixWord ++ tailWord_3664677) baseStart_3664677 baseEnd_3664677 := by
    simpa [prefixWord, tailWord_3664677, baseEnd_3664677] using wordTrace_append hprefix tailTrace_3664677
  have hstable : (prefixWord ++ tailWord_3664677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664677).length < 2 ^ (prefixWord ++ tailWord_3664677).sum := by decide
  have hdescent : baseEnd_3664677 < baseStart_3664677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664708 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3664708 : Nat := 118140960795 + 3664708 * 2 ^ 59
def prefixEnd_3664708 : Nat := 4983230072969 + 3 ^ 40 * 3664708 * 2
def baseEnd_3664708 : Nat := 627252220792384348932107

theorem tailTrace_3664708 : CollatzResearch.WordTrace tailWord_3664708 prefixEnd_3664708 627252220792384348932107 := by
  unfold tailWord_3664708
  simp only [CollatzResearch.WordTrace]
  refine ⟨66831440803698136571237389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89108587738264182094983185 66831440803698136571237389)
  ·
    refine ⟨25061790301386801214214021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66831440803698136571237389 25061790301386801214214021)
    ·
      refine ⟨4699085681510025227665129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25061790301386801214214021 4699085681510025227665129)
      ·
        refine ⟨3524314261132518920748847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4699085681510025227665129 3524314261132518920748847)
        ·
          refine ⟨5286471391698778381123271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3524314261132518920748847 5286471391698778381123271)
          ·
            refine ⟨7929707087548167571684907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286471391698778381123271 7929707087548167571684907)
            ·
              refine ⟨11894560631322251357527361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7929707087548167571684907 11894560631322251357527361)
              ·
                refine ⟨8920920473491688518145521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11894560631322251357527361 8920920473491688518145521)
                ·
                  refine ⟨6690690355118766388609141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8920920473491688518145521 6690690355118766388609141)
                  ·
                    refine ⟨627252220792384348932107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6690690355118766388609141 627252220792384348932107)
                    ·
                      rfl

theorem cell23_3664708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3664708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664708 prefixEnd_3664708 := by exact prefixLift 3664708
  have htrace : WordTrace (prefixWord ++ tailWord_3664708) baseStart_3664708 baseEnd_3664708 := by
    simpa [prefixWord, tailWord_3664708, baseEnd_3664708] using wordTrace_append hprefix tailTrace_3664708
  have hstable : (prefixWord ++ tailWord_3664708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664708).length < 2 ^ (prefixWord ++ tailWord_3664708).sum := by decide
  have hdescent : baseEnd_3664708 < baseStart_3664708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664764 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_3664764 : Nat := 118140960795 + 3664764 * 2 ^ 59
def prefixEnd_3664764 : Nat := 4983230072969 + 3 ^ 40 * 3664764 * 2
def baseEnd_3664764 : Nat := 627261805764601609232021

theorem tailTrace_3664764 : CollatzResearch.WordTrace tailWord_3664764 prefixEnd_3664764 627261805764601609232021 := by
  unfold tailWord_3664764
  simp only [CollatzResearch.WordTrace]
  refine ⟨66832462047596697353256673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89109949396795596471008897 66832462047596697353256673)
  ·
    refine ⟨50124346535697523014942505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66832462047596697353256673 50124346535697523014942505)
    ·
      refine ⟨37593259901773142261206879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50124346535697523014942505 37593259901773142261206879)
      ·
        refine ⟨56389889852659713391810319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37593259901773142261206879 56389889852659713391810319)
        ·
          refine ⟨84584834778989570087715479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56389889852659713391810319 84584834778989570087715479)
          ·
            refine ⟨126877252168484355131573219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84584834778989570087715479 126877252168484355131573219)
            ·
              refine ⟨190315878252726532697359829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126877252168484355131573219 190315878252726532697359829)
              ·
                refine ⟨4460528396548278110094371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 190315878252726532697359829 4460528396548278110094371)
                ·
                  refine ⟨6690792594822417165141557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4460528396548278110094371 6690792594822417165141557)
                  ·
                    refine ⟨627261805764601609232021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6690792594822417165141557 627261805764601609232021)
                    ·
                      rfl

theorem cell23_3664764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_3664764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664764 prefixEnd_3664764 := by exact prefixLift 3664764
  have htrace : WordTrace (prefixWord ++ tailWord_3664764) baseStart_3664764 baseEnd_3664764 := by
    simpa [prefixWord, tailWord_3664764, baseEnd_3664764] using wordTrace_append hprefix tailTrace_3664764
  have hstable : (prefixWord ++ tailWord_3664764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664764).length < 2 ^ (prefixWord ++ tailWord_3664764).sum := by decide
  have hdescent : baseEnd_3664764 < baseStart_3664764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664771 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 2, 3, 2]
def baseStart_3664771 : Nat := 118140960795 + 3664771 * 2 ^ 59
def prefixEnd_3664771 : Nat := 4983230072969 + 3 ^ 40 * 3664771 * 2
def baseEnd_3664771 : Nat := 1881789011658386300308531

theorem tailTrace_3664771 : CollatzResearch.WordTrace tailWord_3664771 prefixEnd_3664771 1881789011658386300308531 := by
  unfold tailWord_3664771
  simp only [CollatzResearch.WordTrace]
  refine ⟨133665179406168034902018167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89110119604112023268012111 133665179406168034902018167)
  ·
    refine ⟨200497769109252052353027251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133665179406168034902018167 200497769109252052353027251)
    ·
      refine ⟨300746653663878078529540877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200497769109252052353027251 300746653663878078529540877)
      ·
        refine ⟨112779995123954279448577829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300746653663878078529540877 112779995123954279448577829)
        ·
          refine ⟨21146249085741427396608343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112779995123954279448577829 21146249085741427396608343)
          ·
            refine ⟨31719373628612141094912515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21146249085741427396608343 31719373628612141094912515)
            ·
              refine ⟨47579060442918211642368773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31719373628612141094912515 47579060442918211642368773)
              ·
                refine ⟨8921073833047164682944145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47579060442918211642368773 8921073833047164682944145)
                ·
                  refine ⟨6690805374785373512208109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8921073833047164682944145 6690805374785373512208109)
                  ·
                    refine ⟨2509052015544515067078041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6690805374785373512208109 2509052015544515067078041)
                    ·
                      refine ⟨1881789011658386300308531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509052015544515067078041 1881789011658386300308531)
                      ·
                        rfl

theorem cell23_3664771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_3664771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664771 prefixEnd_3664771 := by exact prefixLift 3664771
  have htrace : WordTrace (prefixWord ++ tailWord_3664771) baseStart_3664771 baseEnd_3664771 := by
    simpa [prefixWord, tailWord_3664771, baseEnd_3664771] using wordTrace_append hprefix tailTrace_3664771
  have hstable : (prefixWord ++ tailWord_3664771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664771).length < 2 ^ (prefixWord ++ tailWord_3664771).sum := by decide
  have hdescent : baseEnd_3664771 < baseStart_3664771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664801 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3664801 : Nat := 118140960795 + 3664801 * 2 ^ 59
def prefixEnd_3664801 : Nat := 4983230072969 + 3 ^ 40 * 3664801 * 2
def baseEnd_3664801 : Nat := 1881804416078021182933393

theorem tailTrace_3664801 : CollatzResearch.WordTrace tailWord_3664801 prefixEnd_3664801 1881804416078021182933393 := by
  unfold tailWord_3664801
  simp only [CollatzResearch.WordTrace]
  refine ⟨133666273596059350025610257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89110849064039566683740171 133666273596059350025610257)
  ·
    refine ⟨100249705197044512519207693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133666273596059350025610257 100249705197044512519207693)
    ·
      refine ⟨37593639448891692194702885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100249705197044512519207693 37593639448891692194702885)
      ·
        refine ⟨7048807396667192286506791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37593639448891692194702885 7048807396667192286506791)
        ·
          refine ⟨10573211095000788429760187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048807396667192286506791 10573211095000788429760187)
          ·
            refine ⟨15859816642501182644640281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10573211095000788429760187 15859816642501182644640281)
            ·
              refine ⟨11894862481875886983480211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15859816642501182644640281 11894862481875886983480211)
              ·
                refine ⟨17842293722813830475220317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11894862481875886983480211 17842293722813830475220317)
                ·
                  refine ⟨6690860146055186428207619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17842293722813830475220317 6690860146055186428207619)
                  ·
                    refine ⟨10036290219082779642311429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6690860146055186428207619 10036290219082779642311429)
                    ·
                      refine ⟨1881804416078021182933393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10036290219082779642311429 1881804416078021182933393)
                      ·
                        rfl

theorem cell23_3664801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3664801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664801 prefixEnd_3664801 := by exact prefixLift 3664801
  have htrace : WordTrace (prefixWord ++ tailWord_3664801) baseStart_3664801 baseEnd_3664801 := by
    simpa [prefixWord, tailWord_3664801, baseEnd_3664801] using wordTrace_append hprefix tailTrace_3664801
  have hstable : (prefixWord ++ tailWord_3664801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664801).length < 2 ^ (prefixWord ++ tailWord_3664801).sum := by decide
  have hdescent : baseEnd_3664801 < baseStart_3664801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664925 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_3664925 : Nat := 118140960795 + 3664925 * 2 ^ 59
def prefixEnd_3664925 : Nat := 4983230072969 + 3 ^ 40 * 3664925 * 2
def baseEnd_3664925 : Nat := 1881868087679178697782823

theorem tailTrace_3664925 : CollatzResearch.WordTrace tailWord_3664925 prefixEnd_3664925 1881868087679178697782823 := by
  unfold tailWord_3664925
  simp only [CollatzResearch.WordTrace]
  refine ⟨133670796247610119203124229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89113864165073412802082819 133670796247610119203124229)
  ·
    refine ⟨25063274296426897350585793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133670796247610119203124229 25063274296426897350585793)
    ·
      refine ⟨18797455722320173012939345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25063274296426897350585793 18797455722320173012939345)
      ·
        refine ⟨14098091791740129759704509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18797455722320173012939345 14098091791740129759704509)
        ·
          refine ⟨5286784421902548659889191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14098091791740129759704509 5286784421902548659889191)
          ·
            refine ⟨7930176632853822989833787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286784421902548659889191 7930176632853822989833787)
            ·
              refine ⟨11895264949280734484750681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930176632853822989833787 11895264949280734484750681)
              ·
                refine ⟨8921448711960550863563011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11895264949280734484750681 8921448711960550863563011)
                ·
                  refine ⟨13382173067940826295344517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8921448711960550863563011 13382173067940826295344517)
                  ·
                    refine ⟨2509157450238904930377097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13382173067940826295344517 2509157450238904930377097)
                    ·
                      refine ⟨1881868087679178697782823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509157450238904930377097 1881868087679178697782823)
                      ·
                        rfl

theorem cell23_3664925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_3664925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664925 prefixEnd_3664925 := by exact prefixLift 3664925
  have htrace : WordTrace (prefixWord ++ tailWord_3664925) baseStart_3664925 baseEnd_3664925 := by
    simpa [prefixWord, tailWord_3664925, baseEnd_3664925] using wordTrace_append hprefix tailTrace_3664925
  have hstable : (prefixWord ++ tailWord_3664925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664925).length < 2 ^ (prefixWord ++ tailWord_3664925).sum := by decide
  have hdescent : baseEnd_3664925 < baseStart_3664925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664942 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_3664942 : Nat := 118140960795 + 3664942 * 2 ^ 59
def prefixEnd_3664942 : Nat := 4983230072969 + 3 ^ 40 * 3664942 * 2
def baseEnd_3664942 : Nat := 1881876816850305131270245

theorem tailTrace_3664942 : CollatzResearch.WordTrace tailWord_3664942 prefixEnd_3664942 1881876816850305131270245 := by
  unfold tailWord_3664942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16708927036068566388311635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89114277525699020737662053 16708927036068566388311635)
  ·
    refine ⟨25063390554102849582467453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16708927036068566388311635 25063390554102849582467453)
    ·
      refine ⟨9398771457788568593425295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25063390554102849582467453 9398771457788568593425295)
      ·
        refine ⟨14098157186682852890137943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9398771457788568593425295 14098157186682852890137943)
        ·
          refine ⟨21147235780024279335206915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14098157186682852890137943 21147235780024279335206915)
          ·
            refine ⟨31720853670036419002810373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21147235780024279335206915 31720853670036419002810373)
            ·
              refine ⟨5947660063131828563026945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31720853670036419002810373 5947660063131828563026945)
              ·
                refine ⟨4460745047348871422270209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5947660063131828563026945 4460745047348871422270209)
                ·
                  refine ⟨3345558785511653566702657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4460745047348871422270209 3345558785511653566702657)
                  ·
                    refine ⟨2509169089133740175026993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3345558785511653566702657 2509169089133740175026993)
                    ·
                      refine ⟨1881876816850305131270245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509169089133740175026993 1881876816850305131270245)
                      ·
                        rfl

theorem cell23_3664942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_3664942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664942 prefixEnd_3664942 := by exact prefixLift 3664942
  have htrace : WordTrace (prefixWord ++ tailWord_3664942) baseStart_3664942 baseEnd_3664942 := by
    simpa [prefixWord, tailWord_3664942, baseEnd_3664942] using wordTrace_append hprefix tailTrace_3664942
  have hstable : (prefixWord ++ tailWord_3664942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664942).length < 2 ^ (prefixWord ++ tailWord_3664942).sum := by decide
  have hdescent : baseEnd_3664942 < baseStart_3664942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664958 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3664958 : Nat := 118140960795 + 3664958 * 2 ^ 59
def prefixEnd_3664958 : Nat := 4983230072969 + 3 ^ 40 * 3664958 * 2
def baseEnd_3664958 : Nat := 1881885032540777068670171

theorem tailTrace_3664958 : CollatzResearch.WordTrace tailWord_3664958 prefixEnd_3664958 1881885032540777068670171 := by
  unfold tailWord_3664958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16708999982061320729884441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89114666570993710559383685 16708999982061320729884441)
  ·
    refine ⟨12531749986545990547413331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16708999982061320729884441 12531749986545990547413331)
    ·
      refine ⟨18797624979818985821119997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12531749986545990547413331 18797624979818985821119997)
      ·
        refine ⟨7049109367432119682919999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18797624979818985821119997 7049109367432119682919999)
        ·
          refine ⟨10573664051148179524379999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7049109367432119682919999 10573664051148179524379999)
          ·
            refine ⟨15860496076722269286569999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10573664051148179524379999 15860496076722269286569999)
            ·
              refine ⟨23790744115083403929854999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15860496076722269286569999 23790744115083403929854999)
              ·
                refine ⟨35686116172625105894782499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23790744115083403929854999 35686116172625105894782499)
                ·
                  refine ⟨53529174258937658842173749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35686116172625105894782499 53529174258937658842173749)
                  ·
                    refine ⟨5018360086775405516453789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53529174258937658842173749 5018360086775405516453789)
                    ·
                      refine ⟨1881885032540777068670171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5018360086775405516453789 1881885032540777068670171)
                      ·
                        rfl

theorem cell23_3664958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3664958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664958 prefixEnd_3664958 := by exact prefixLift 3664958
  have htrace : WordTrace (prefixWord ++ tailWord_3664958) baseStart_3664958 baseEnd_3664958 := by
    simpa [prefixWord, tailWord_3664958, baseEnd_3664958] using wordTrace_append hprefix tailTrace_3664958
  have hstable : (prefixWord ++ tailWord_3664958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664958).length < 2 ^ (prefixWord ++ tailWord_3664958).sum := by decide
  have hdescent : baseEnd_3664958 < baseStart_3664958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664978 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_3664978 : Nat := 118140960795 + 3664978 * 2 ^ 59
def prefixEnd_3664978 : Nat := 4983230072969 + 3 ^ 40 * 3664978 * 2
def baseEnd_3664978 : Nat := 627298434051288996806693

theorem tailTrace_3664978 : CollatzResearch.WordTrace tailWord_3664978 prefixEnd_3664978 627298434051288996806693 := by
  unfold tailWord_3664978
  simp only [CollatzResearch.WordTrace]
  refine ⟨33418182329104527313700897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89115152877612072836535725 33418182329104527313700897)
  ·
    refine ⟨25063636746828395485275673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33418182329104527313700897 25063636746828395485275673)
    ·
      refine ⟨18797727560121296613956755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25063636746828395485275673 18797727560121296613956755)
      ·
        refine ⟨28196591340181944920935133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18797727560121296613956755 28196591340181944920935133)
        ·
          refine ⟨10573721752568229345350675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28196591340181944920935133 10573721752568229345350675)
          ·
            refine ⟨15860582628852344018026013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10573721752568229345350675 15860582628852344018026013)
            ·
              refine ⟨5947718485819629006759755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15860582628852344018026013 5947718485819629006759755)
              ·
                refine ⟨8921577728729443510139633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947718485819629006759755 8921577728729443510139633)
                ·
                  refine ⟨6691183296547082632604725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8921577728729443510139633 6691183296547082632604725)
                  ·
                    refine ⟨627298434051288996806693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6691183296547082632604725 627298434051288996806693)
                    ·
                      rfl

theorem cell23_3664978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_3664978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664978 prefixEnd_3664978 := by exact prefixLift 3664978
  have htrace : WordTrace (prefixWord ++ tailWord_3664978) baseStart_3664978 baseEnd_3664978 := by
    simpa [prefixWord, tailWord_3664978, baseEnd_3664978] using wordTrace_append hprefix tailTrace_3664978
  have hstable : (prefixWord ++ tailWord_3664978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664978).length < 2 ^ (prefixWord ++ tailWord_3664978).sum := by decide
  have hdescent : baseEnd_3664978 < baseStart_3664978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664981 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3664981 : Nat := 118140960795 + 3664981 * 2 ^ 59
def prefixEnd_3664981 : Nat := 4983230072969 + 3 ^ 40 * 3664981 * 2
def baseEnd_3664981 : Nat := 1881896842595830478682565

theorem tailTrace_3664981 : CollatzResearch.WordTrace tailWord_3664981 prefixEnd_3664981 1881896842595830478682565 := by
  unfold tailWord_3664981
  simp only [CollatzResearch.WordTrace]
  refine ⟨133672838735407240767162797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89115225823604827178108531 133672838735407240767162797)
  ·
    refine ⟨50127314525777715287686049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133672838735407240767162797 50127314525777715287686049)
    ·
      refine ⟨37595485894333286465764537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50127314525777715287686049 37595485894333286465764537)
      ·
        refine ⟨28196614420749964849323403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37595485894333286465764537 28196614420749964849323403)
        ·
          refine ⟨42294921631124947273985105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28196614420749964849323403 42294921631124947273985105)
          ·
            refine ⟨31721191223343710455488829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42294921631124947273985105 31721191223343710455488829)
            ·
              refine ⟨11895446708753891420808311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31721191223343710455488829 11895446708753891420808311)
              ·
                refine ⟨17843170063130837131212467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11895446708753891420808311 17843170063130837131212467)
                ·
                  refine ⟨26764755094696255696818701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17843170063130837131212467 26764755094696255696818701)
                  ·
                    refine ⟨10036783160511095886307013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26764755094696255696818701 10036783160511095886307013)
                    ·
                      refine ⟨1881896842595830478682565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10036783160511095886307013 1881896842595830478682565)
                      ·
                        rfl

theorem cell23_3664981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3664981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664981 prefixEnd_3664981 := by exact prefixLift 3664981
  have htrace : WordTrace (prefixWord ++ tailWord_3664981) baseStart_3664981 baseEnd_3664981 := by
    simpa [prefixWord, tailWord_3664981, baseEnd_3664981] using wordTrace_append hprefix tailTrace_3664981
  have hstable : (prefixWord ++ tailWord_3664981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664981).length < 2 ^ (prefixWord ++ tailWord_3664981).sum := by decide
  have hdescent : baseEnd_3664981 < baseStart_3664981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664991 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 5, 4]
def baseStart_3664991 : Nat := 118140960795 + 3664991 * 2 ^ 59
def prefixEnd_3664991 : Nat := 4983230072969 + 3 ^ 40 * 3664991 * 2
def baseEnd_3664991 : Nat := 627300659134125146519173

theorem tailTrace_3664991 : CollatzResearch.WordTrace tailWord_3664991 prefixEnd_3664991 627300659134125146519173 := by
  unfold tailWord_3664991
  simp only [CollatzResearch.WordTrace]
  refine ⟨133673203465371012475026827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89115468976914008316684551 133673203465371012475026827)
  ·
    refine ⟨200509805198056518712540241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133673203465371012475026827 200509805198056518712540241)
    ·
      refine ⟨150382353898542389034405181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200509805198056518712540241 150382353898542389034405181)
      ·
        refine ⟨56393382711953395887901943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150382353898542389034405181 56393382711953395887901943)
        ·
          refine ⟨84590074067930093831852915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56393382711953395887901943 84590074067930093831852915)
          ·
            refine ⟨126885111101895140747779373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84590074067930093831852915 126885111101895140747779373)
            ·
              refine ⟨47581916663210677780417265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126885111101895140747779373 47581916663210677780417265)
              ·
                refine ⟨35686437497408008335312949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47581916663210677780417265 35686437497408008335312949)
                ·
                  refine ⟨3345603515382000781435589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35686437497408008335312949 3345603515382000781435589)
                  ·
                    refine ⟨627300659134125146519173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345603515382000781435589 627300659134125146519173)
                    ·
                      rfl

theorem cell23_3664991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 4].length) (baseStart_3664991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3664991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3664991 prefixEnd_3664991 := by exact prefixLift 3664991
  have htrace : WordTrace (prefixWord ++ tailWord_3664991) baseStart_3664991 baseEnd_3664991 := by
    simpa [prefixWord, tailWord_3664991, baseEnd_3664991] using wordTrace_append hprefix tailTrace_3664991
  have hstable : (prefixWord ++ tailWord_3664991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664991).length < 2 ^ (prefixWord ++ tailWord_3664991).sum := by decide
  have hdescent : baseEnd_3664991 < baseStart_3664991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665008 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 3, 4]
def baseStart_3665008 : Nat := 118140960795 + 3665008 * 2 ^ 59
def prefixEnd_3665008 : Nat := 4983230072969 + 3 ^ 40 * 3665008 * 2
def baseEnd_3665008 : Nat := 627303568857833957681647

theorem tailTrace_3665008 : CollatzResearch.WordTrace tailWord_3665008 prefixEnd_3665008 627303568857833957681647 := by
  unfold tailWord_3665008
  simp only [CollatzResearch.WordTrace]
  refine ⟨66836911753154712189197839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89115882337539616252263785 66836911753154712189197839)
  ·
    refine ⟨100255367629732068283796759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66836911753154712189197839 100255367629732068283796759)
    ·
      refine ⟨150383051444598102425695139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100255367629732068283796759 150383051444598102425695139)
      ·
        refine ⟨225574577166897153638542709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150383051444598102425695139 225574577166897153638542709)
        ·
          refine ⟨21147616609396608153613379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225574577166897153638542709 21147616609396608153613379)
          ·
            refine ⟨31721424914094912230420069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21147616609396608153613379 31721424914094912230420069)
            ·
              refine ⟨5947767171392796043203763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31721424914094912230420069 5947767171392796043203763)
              ·
                refine ⟨8921650757089194064805645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947767171392796043203763 8921650757089194064805645)
                ·
                  refine ⟨3345619033908447774302117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8921650757089194064805645 3345619033908447774302117)
                  ·
                    refine ⟨627303568857833957681647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345619033908447774302117 627303568857833957681647)
                    ·
                      rfl

theorem cell23_3665008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 4].length) (baseStart_3665008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665008 prefixEnd_3665008 := by exact prefixLift 3665008
  have htrace : WordTrace (prefixWord ++ tailWord_3665008) baseStart_3665008 baseEnd_3665008 := by
    simpa [prefixWord, tailWord_3665008, baseEnd_3665008] using wordTrace_append hprefix tailTrace_3665008
  have hstable : (prefixWord ++ tailWord_3665008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665008).length < 2 ^ (prefixWord ++ tailWord_3665008).sum := by decide
  have hdescent : baseEnd_3665008 < baseStart_3665008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665031 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_3665031 : Nat := 118140960795 + 3665031 * 2 ^ 59
def prefixEnd_3665031 : Nat := 4983230072969 + 3 ^ 40 * 3665031 * 2
def baseEnd_3665031 : Nat := 1881922516628555283057335

theorem tailTrace_3665031 : CollatzResearch.WordTrace tailWord_3665031 prefixEnd_3665031 1881922516628555283057335 := by
  unfold tailWord_3665031
  simp only [CollatzResearch.WordTrace]
  refine ⟨133674662385226099306482947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89116441590150732870988631 133674662385226099306482947)
  ·
    refine ⟨200511993577839148959724421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133674662385226099306482947 200511993577839148959724421)
    ·
      refine ⟨37595998795844840429948329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200511993577839148959724421 37595998795844840429948329)
      ·
        refine ⟨28196999096883630322461247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37595998795844840429948329 28196999096883630322461247)
        ·
          refine ⟨42295498645325445483691871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28196999096883630322461247 42295498645325445483691871)
          ·
            refine ⟨63443247967988168225537807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42295498645325445483691871 63443247967988168225537807)
            ·
              refine ⟨95164871951982252338306711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63443247967988168225537807 95164871951982252338306711)
              ·
                refine ⟨142747307927973378507460067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95164871951982252338306711 142747307927973378507460067)
                ·
                  refine ⟨214120961891960067761190101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142747307927973378507460067 214120961891960067761190101)
                  ·
                    refine ⟨5018460044342814088152893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 214120961891960067761190101 5018460044342814088152893)
                    ·
                      refine ⟨1881922516628555283057335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5018460044342814088152893 1881922516628555283057335)
                      ·
                        rfl

theorem cell23_3665031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_3665031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665031 prefixEnd_3665031 := by exact prefixLift 3665031
  have htrace : WordTrace (prefixWord ++ tailWord_3665031) baseStart_3665031 baseEnd_3665031 := by
    simpa [prefixWord, tailWord_3665031, baseEnd_3665031] using wordTrace_append hprefix tailTrace_3665031
  have hstable : (prefixWord ++ tailWord_3665031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665031).length < 2 ^ (prefixWord ++ tailWord_3665031).sum := by decide
  have hdescent : baseEnd_3665031 < baseStart_3665031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665042 : List Nat := [3, 2, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3665042 : Nat := 118140960795 + 3665042 * 2 ^ 59
def prefixEnd_3665042 : Nat := 4983230072969 + 3 ^ 40 * 3665042 * 2
def baseEnd_3665042 : Nat := 627309388305251580006595

theorem tailTrace_3665042 : CollatzResearch.WordTrace tailWord_3665042 prefixEnd_3665042 627309388305251580006595 := by
  unfold tailWord_3665042
  simp only [CollatzResearch.WordTrace]
  refine ⟨33418765897046562046283345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89116709058790832123422253 33418765897046562046283345)
  ·
    refine ⟨25064074422784921534712509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33418765897046562046283345 25064074422784921534712509)
    ·
      refine ⟨9399027908544345575517191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25064074422784921534712509 9399027908544345575517191)
      ·
        refine ⟨14098541862816518363275787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9399027908544345575517191 14098541862816518363275787)
        ·
          refine ⟨21147812794224777544913681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14098541862816518363275787 21147812794224777544913681)
          ·
            refine ⟨15860859595668583158685261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21147812794224777544913681 15860859595668583158685261)
            ·
              refine ⟨5947822348375718684506973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15860859595668583158685261 5947822348375718684506973)
              ·
                refine ⟨2230433380640894506690115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5947822348375718684506973 2230433380640894506690115)
                ·
                  refine ⟨3345650070961341760035173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230433380640894506690115 3345650070961341760035173)
                  ·
                    refine ⟨627309388305251580006595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345650070961341760035173 627309388305251580006595)
                    ·
                      rfl

theorem cell23_3665042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3665042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665042 prefixEnd_3665042 := by exact prefixLift 3665042
  have htrace : WordTrace (prefixWord ++ tailWord_3665042) baseStart_3665042 baseEnd_3665042 := by
    simpa [prefixWord, tailWord_3665042, baseEnd_3665042] using wordTrace_append hprefix tailTrace_3665042
  have hstable : (prefixWord ++ tailWord_3665042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665042).length < 2 ^ (prefixWord ++ tailWord_3665042).sum := by decide
  have hdescent : baseEnd_3665042 < baseStart_3665042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665098 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_3665098 : Nat := 118140960795 + 3665098 * 2 ^ 59
def prefixEnd_3665098 : Nat := 4983230072969 + 3 ^ 40 * 3665098 * 2
def baseEnd_3665098 : Nat := 627318973277468840306509

theorem tailTrace_3665098 : CollatzResearch.WordTrace tailWord_3665098 prefixEnd_3665098 627318973277468840306509 := by
  unfold tailWord_3665098
  simp only [CollatzResearch.WordTrace]
  refine ⟨33419276518995842437292987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89118070717322246499447965 33419276518995842437292987)
  ·
    refine ⟨50128914778493763655939481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33419276518995842437292987 50128914778493763655939481)
    ·
      refine ⟨37596686083870322741954611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50128914778493763655939481 37596686083870322741954611)
      ·
        refine ⟨56395029125805484112931917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37596686083870322741954611 56395029125805484112931917)
        ·
          refine ⟨21148135922177056542349469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56395029125805484112931917 21148135922177056542349469)
          ·
            refine ⟨7930550970816396203381051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21148135922177056542349469 7930550970816396203381051)
            ·
              refine ⟨11895826456224594305071577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930550970816396203381051 11895826456224594305071577)
              ·
                refine ⟨8921869842168445728803683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11895826456224594305071577 8921869842168445728803683)
                ·
                  refine ⟨13382804763252668593205525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8921869842168445728803683 13382804763252668593205525)
                  ·
                    refine ⟨627318973277468840306509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13382804763252668593205525 627318973277468840306509)
                    ·
                      rfl

theorem cell23_3665098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_3665098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665098 prefixEnd_3665098 := by exact prefixLift 3665098
  have htrace : WordTrace (prefixWord ++ tailWord_3665098) baseStart_3665098 baseEnd_3665098 := by
    simpa [prefixWord, tailWord_3665098, baseEnd_3665098] using wordTrace_append hprefix tailTrace_3665098
  have hstable : (prefixWord ++ tailWord_3665098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665098).length < 2 ^ (prefixWord ++ tailWord_3665098).sum := by decide
  have hdescent : baseEnd_3665098 < baseStart_3665098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665102 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_3665102 : Nat := 118140960795 + 3665102 * 2 ^ 59
def prefixEnd_3665102 : Nat := 4983230072969 + 3 ^ 40 * 3665102 * 2
def baseEnd_3665102 : Nat := 627319657918341501756503

theorem tailTrace_3665102 : CollatzResearch.WordTrace tailWord_3665102 prefixEnd_3665102 627319657918341501756503 := by
  unfold tailWord_3665102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16709656495996109804039695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89118167978645918954878373 16709656495996109804039695)
  ·
    refine ⟨25064484743994164706059543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16709656495996109804039695 25064484743994164706059543)
    ·
      refine ⟨37596727115991247059089315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25064484743994164706059543 37596727115991247059089315)
      ·
        refine ⟨56395090673986870588633973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37596727115991247059089315 56395090673986870588633973)
        ·
          refine ⟨5287039750686269117684435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56395090673986870588633973 5287039750686269117684435)
          ·
            refine ⟨7930559626029403676526653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287039750686269117684435 7930559626029403676526653)
            ·
              refine ⟨2973959859761026378697495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7930559626029403676526653 2973959859761026378697495)
              ·
                refine ⟨4460939789641539568046243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973959859761026378697495 4460939789641539568046243)
                ·
                  refine ⟨6691409684462309352069365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4460939789641539568046243 6691409684462309352069365)
                  ·
                    refine ⟨627319657918341501756503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6691409684462309352069365 627319657918341501756503)
                    ·
                      rfl

theorem cell23_3665102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_3665102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665102 prefixEnd_3665102 := by exact prefixLift 3665102
  have htrace : WordTrace (prefixWord ++ tailWord_3665102) baseStart_3665102 baseEnd_3665102 := by
    simpa [prefixWord, tailWord_3665102, baseEnd_3665102] using wordTrace_append hprefix tailTrace_3665102
  have hstable : (prefixWord ++ tailWord_3665102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665102).length < 2 ^ (prefixWord ++ tailWord_3665102).sum := by decide
  have hdescent : baseEnd_3665102 < baseStart_3665102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665135 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 4]
def baseStart_3665135 : Nat := 118140960795 + 3665135 * 2 ^ 59
def prefixEnd_3665135 : Nat := 4983230072969 + 3 ^ 40 * 3665135 * 2
def baseEnd_3665135 : Nat := 1881975918616622876156857

theorem tailTrace_3665135 : CollatzResearch.WordTrace tailWord_3665135 prefixEnd_3665135 1881975918616622876156857 := by
  unfold tailWord_3665135
  simp only [CollatzResearch.WordTrace]
  refine ⟨133678455576849325068268859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89118970384566216712179239 133678455576849325068268859)
  ·
    refine ⟨200517683365273987602403289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133678455576849325068268859 200517683365273987602403289)
    ·
      refine ⟨150388262523955490701802467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200517683365273987602403289 150388262523955490701802467)
      ·
        refine ⟨225582393785933236052703701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150388262523955490701802467 225582393785933236052703701)
        ·
          refine ⟨5287087354357810219985243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 225582393785933236052703701 5287087354357810219985243)
          ·
            refine ⟨7930631031536715329977865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287087354357810219985243 7930631031536715329977865)
            ·
              refine ⟨5947973273652536497483399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7930631031536715329977865 5947973273652536497483399)
              ·
                refine ⟨8921959910478804746225099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947973273652536497483399 8921959910478804746225099)
                ·
                  refine ⟨13382939865718207119337649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8921959910478804746225099 13382939865718207119337649)
                  ·
                    refine ⟨10037204899288655339503237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13382939865718207119337649 10037204899288655339503237)
                    ·
                      refine ⟨1881975918616622876156857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10037204899288655339503237 1881975918616622876156857)
                      ·
                        rfl

theorem cell23_3665135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_3665135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665135 prefixEnd_3665135 := by exact prefixLift 3665135
  have htrace : WordTrace (prefixWord ++ tailWord_3665135) baseStart_3665135 baseEnd_3665135 := by
    simpa [prefixWord, tailWord_3665135, baseEnd_3665135] using wordTrace_append hprefix tailTrace_3665135
  have hstable : (prefixWord ++ tailWord_3665135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665135).length < 2 ^ (prefixWord ++ tailWord_3665135).sum := by decide
  have hdescent : baseEnd_3665135 < baseStart_3665135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665156 : List Nat := [2, 3, 2, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_3665156 : Nat := 118140960795 + 3665156 * 2 ^ 59
def prefixEnd_3665156 : Nat := 4983230072969 + 3 ^ 40 * 3665156 * 2
def baseEnd_3665156 : Nat := 1881986701710367293994261

theorem tailTrace_3665156 : CollatzResearch.WordTrace tailWord_3665156 prefixEnd_3665156 1881986701710367293994261 := by
  unfold tailWord_3665156
  simp only [CollatzResearch.WordTrace]
  refine ⟨66839610754886622827391661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89119481006515497103188881 66839610754886622827391661)
  ·
    refine ⟨25064854033082483560271873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66839610754886622827391661 25064854033082483560271873)
    ·
      refine ⟨18798640524811862670203905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25064854033082483560271873 18798640524811862670203905)
      ·
        refine ⟨14098980393608897002652929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18798640524811862670203905 14098980393608897002652929)
        ·
          refine ⟨10574235295206672751989697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14098980393608897002652929 10574235295206672751989697)
          ·
            refine ⟨7930676471405004563992273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10574235295206672751989697 7930676471405004563992273)
            ·
              refine ⟨5948007353553753422994205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7930676471405004563992273 5948007353553753422994205)
              ·
                refine ⟨2230502757582657533622827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5948007353553753422994205 2230502757582657533622827)
                ·
                  refine ⟨3345754136373986300434241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230502757582657533622827 3345754136373986300434241)
                  ·
                    refine ⟨2509315602280489725325681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3345754136373986300434241 2509315602280489725325681)
                    ·
                      refine ⟨1881986701710367293994261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509315602280489725325681 1881986701710367293994261)
                      ·
                        rfl

theorem cell23_3665156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_3665156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665156 prefixEnd_3665156 := by exact prefixLift 3665156
  have htrace : WordTrace (prefixWord ++ tailWord_3665156) baseStart_3665156 baseEnd_3665156 := by
    simpa [prefixWord, tailWord_3665156, baseEnd_3665156] using wordTrace_append hprefix tailTrace_3665156
  have hstable : (prefixWord ++ tailWord_3665156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665156).length < 2 ^ (prefixWord ++ tailWord_3665156).sum := by decide
  have hdescent : baseEnd_3665156 < baseStart_3665156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665188 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_3665188 : Nat := 118140960795 + 3665188 * 2 ^ 59
def prefixEnd_3665188 : Nat := 4983230072969 + 3 ^ 40 * 3665188 * 2
def baseEnd_3665188 : Nat := 627334377697103722931371

theorem tailTrace_3665188 : CollatzResearch.WordTrace tailWord_3665188 prefixEnd_3665188 627334377697103722931371 := by
  unfold tailWord_3665188
  simp only [CollatzResearch.WordTrace]
  refine ⟨66840194322828657559974109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89120259097104876746632145 66840194322828657559974109)
  ·
    refine ⟨25065072871060746584990291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66840194322828657559974109 25065072871060746584990291)
    ·
      refine ⟨37597609306591119877485437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25065072871060746584990291 37597609306591119877485437)
      ·
        refine ⟨14099103489971669954057039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37597609306591119877485437 14099103489971669954057039)
        ·
          refine ⟨21148655234957504931085559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14099103489971669954057039 21148655234957504931085559)
          ·
            refine ⟨31722982852436257396628339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21148655234957504931085559 31722982852436257396628339)
            ·
              refine ⟨47584474278654386094942509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31722982852436257396628339 47584474278654386094942509)
              ·
                refine ⟨17844177854495394785603441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47584474278654386094942509 17844177854495394785603441)
                ·
                  refine ⟨13383133390871546089202581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17844177854495394785603441 13383133390871546089202581)
                  ·
                    refine ⟨627334377697103722931371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13383133390871546089202581 627334377697103722931371)
                    ·
                      rfl

theorem cell23_3665188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_3665188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665188 prefixEnd_3665188 := by exact prefixLift 3665188
  have htrace : WordTrace (prefixWord ++ tailWord_3665188) baseStart_3665188 baseEnd_3665188 := by
    simpa [prefixWord, tailWord_3665188, baseEnd_3665188] using wordTrace_append hprefix tailTrace_3665188
  have hstable : (prefixWord ++ tailWord_3665188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665188).length < 2 ^ (prefixWord ++ tailWord_3665188).sum := by decide
  have hdescent : baseEnd_3665188 < baseStart_3665188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665189 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 2, 1, 3]
def baseStart_3665189 : Nat := 118140960795 + 3665189 * 2 ^ 59
def prefixEnd_3665189 : Nat := 4983230072969 + 3 ^ 40 * 3665189 * 2
def baseEnd_3665189 : Nat := 1882003646571965664881609

theorem tailTrace_3665189 : CollatzResearch.WordTrace tailWord_3665189 prefixEnd_3665189 1882003646571965664881609 := by
  unfold tailWord_3665189
  simp only [CollatzResearch.WordTrace]
  refine ⟨133680425118653692290734621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89120283412435794860489747 133680425118653692290734621)
  ·
    refine ⟨50130159419495134609025483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133680425118653692290734621 50130159419495134609025483)
    ·
      refine ⟨75195239129242701913538225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50130159419495134609025483 75195239129242701913538225)
      ·
        refine ⟨56396429346932026435153669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75195239129242701913538225 56396429346932026435153669)
        ·
          refine ⟨10574330502549754956591313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56396429346932026435153669 10574330502549754956591313)
          ·
            refine ⟨7930747876912316217443485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10574330502549754956591313 7930747876912316217443485)
            ·
              refine ⟨2974030453842118581541307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7930747876912316217443485 2974030453842118581541307)
              ·
                refine ⟨4461045680763177872311961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974030453842118581541307 4461045680763177872311961)
                ·
                  refine ⟨3345784260572383404233971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461045680763177872311961 3345784260572383404233971)
                  ·
                    refine ⟨5018676390858575106350957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3345784260572383404233971 5018676390858575106350957)
                    ·
                      refine ⟨1882003646571965664881609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5018676390858575106350957 1882003646571965664881609)
                      ·
                        rfl

theorem cell23_3665189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_3665189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665189 prefixEnd_3665189 := by exact prefixLift 3665189
  have htrace : WordTrace (prefixWord ++ tailWord_3665189) baseStart_3665189 baseEnd_3665189 := by
    simpa [prefixWord, tailWord_3665189, baseEnd_3665189] using wordTrace_append hprefix tailTrace_3665189
  have hstable : (prefixWord ++ tailWord_3665189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665189).length < 2 ^ (prefixWord ++ tailWord_3665189).sum := by decide
  have hdescent : baseEnd_3665189 < baseStart_3665189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665212 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_3665212 : Nat := 118140960795 + 3665212 * 2 ^ 59
def prefixEnd_3665212 : Nat := 4983230072969 + 3 ^ 40 * 3665212 * 2
def baseEnd_3665212 : Nat := 1882015456627019074894003

theorem tailTrace_3665212 : CollatzResearch.WordTrace tailWord_3665212 prefixEnd_3665212 1882015456627019074894003 := by
  unfold tailWord_3665212
  simp only [CollatzResearch.WordTrace]
  refine ⟨66840631998785183609410945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89120842665046911479214593 66840631998785183609410945)
  ·
    refine ⟨50130473999088887707058209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66840631998785183609410945 50130473999088887707058209)
    ·
      refine ⟨37597855499316665780293657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50130473999088887707058209 37597855499316665780293657)
      ·
        refine ⟨28198391624487499335220243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37597855499316665780293657 28198391624487499335220243)
        ·
          refine ⟨42297587436731249002830365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28198391624487499335220243 42297587436731249002830365)
          ·
            refine ⟨15861595288774218376061387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42297587436731249002830365 15861595288774218376061387)
            ·
              refine ⟨23792392933161327564092081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15861595288774218376061387 23792392933161327564092081)
              ·
                refine ⟨17844294699870995673069061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23792392933161327564092081 17844294699870995673069061)
                ·
                  refine ⟨3345805256225811688700449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17844294699870995673069061 3345805256225811688700449)
                  ·
                    refine ⟨2509353942169358766525337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3345805256225811688700449 2509353942169358766525337)
                    ·
                      refine ⟨1882015456627019074894003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509353942169358766525337 1882015456627019074894003)
                      ·
                        rfl

theorem cell23_3665212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_3665212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665212 prefixEnd_3665212 := by exact prefixLift 3665212
  have htrace : WordTrace (prefixWord ++ tailWord_3665212) baseStart_3665212 baseEnd_3665212 := by
    simpa [prefixWord, tailWord_3665212, baseEnd_3665212] using wordTrace_append hprefix tailTrace_3665212
  have hstable : (prefixWord ++ tailWord_3665212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665212).length < 2 ^ (prefixWord ++ tailWord_3665212).sum := by decide
  have hdescent : baseEnd_3665212 < baseStart_3665212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665285 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_3665285 : Nat := 118140960795 + 3665285 * 2 ^ 59
def prefixEnd_3665285 : Nat := 4983230072969 + 3 ^ 40 * 3665285 * 2
def baseEnd_3665285 : Nat := 1882052940714797289281167

theorem tailTrace_3665285 : CollatzResearch.WordTrace tailWord_3665285 prefixEnd_3665285 1882052940714797289281167 := by
  unfold tailWord_3665285
  simp only [CollatzResearch.WordTrace]
  refine ⟨133683926526305900686229309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89122617684203933790819539 133683926526305900686229309)
  ·
    refine ⟨50131472447364712757335991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133683926526305900686229309 50131472447364712757335991)
    ·
      refine ⟨75197208671047069136003987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50131472447364712757335991 75197208671047069136003987)
      ·
        refine ⟨112795813006570603704005981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75197208671047069136003987 112795813006570603704005981)
        ·
          refine ⟨42298429877463976389002243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112795813006570603704005981 42298429877463976389002243)
          ·
            refine ⟨63447644816195964583503365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42298429877463976389002243 63447644816195964583503365)
            ·
              refine ⟨11896433403036743359406881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63447644816195964583503365 11896433403036743359406881)
              ·
                refine ⟨8922325052277557519555161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11896433403036743359406881 8922325052277557519555161)
                ·
                  refine ⟨6691743789208168139666371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8922325052277557519555161 6691743789208168139666371)
                  ·
                    refine ⟨10037615683812252209499557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6691743789208168139666371 10037615683812252209499557)
                    ·
                      refine ⟨1882052940714797289281167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10037615683812252209499557 1882052940714797289281167)
                      ·
                        rfl

theorem cell23_3665285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_3665285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665285 prefixEnd_3665285 := by exact prefixLift 3665285
  have htrace : WordTrace (prefixWord ++ tailWord_3665285) baseStart_3665285 baseEnd_3665285 := by
    simpa [prefixWord, tailWord_3665285, baseEnd_3665285] using wordTrace_append hprefix tailTrace_3665285
  have hstable : (prefixWord ++ tailWord_3665285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665285).length < 2 ^ (prefixWord ++ tailWord_3665285).sum := by decide
  have hdescent : baseEnd_3665285 < baseStart_3665285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665329 : List Nat := [1, 2, 2, 4, 1, 1, 4, 3, 1, 4]
def baseStart_3665329 : Nat := 118140960795 + 3665329 * 2 ^ 59
def prefixEnd_3665329 : Nat := 4983230072969 + 3 ^ 40 * 3665329 * 2
def baseEnd_3665329 : Nat := 627358511287865039043655

theorem tailTrace_3665329 : CollatzResearch.WordTrace tailWord_3665329 prefixEnd_3665329 627358511287865039043655 := by
  unfold tailWord_3665329
  simp only [CollatzResearch.WordTrace]
  refine ⟨133685531338146496200831041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89123687558764330800554027 133685531338146496200831041)
  ·
    refine ⟨100264148503609872150623281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133685531338146496200831041 100264148503609872150623281)
    ·
      refine ⟨75198111377707404112967461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100264148503609872150623281 75198111377707404112967461)
      ·
        refine ⟨14099645883320138271181399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75198111377707404112967461 14099645883320138271181399)
        ·
          refine ⟨21149468824980207406772099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14099645883320138271181399 21149468824980207406772099)
          ·
            refine ⟨31724203237470311110158149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21149468824980207406772099 31724203237470311110158149)
            ·
              refine ⟨5948288107025683333154653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31724203237470311110158149 5948288107025683333154653)
              ·
                refine ⟨2230608040134631249932995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5948288107025683333154653 2230608040134631249932995)
                ·
                  refine ⟨3345912060201946874899493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230608040134631249932995 3345912060201946874899493)
                  ·
                    refine ⟨627358511287865039043655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345912060201946874899493 627358511287865039043655)
                    ·
                      rfl

theorem cell23_3665329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_3665329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665329 prefixEnd_3665329 := by exact prefixLift 3665329
  have htrace : WordTrace (prefixWord ++ tailWord_3665329) baseStart_3665329 baseEnd_3665329 := by
    simpa [prefixWord, tailWord_3665329, baseEnd_3665329] using wordTrace_append hprefix tailTrace_3665329
  have hstable : (prefixWord ++ tailWord_3665329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665329).length < 2 ^ (prefixWord ++ tailWord_3665329).sum := by decide
  have hdescent : baseEnd_3665329 < baseStart_3665329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665392 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 4]
def baseStart_3665392 : Nat := 118140960795 + 3665392 * 2 ^ 59
def prefixEnd_3665392 : Nat := 4983230072969 + 3 ^ 40 * 3665392 * 2
def baseEnd_3665392 : Nat := 1882107883144828370643175

theorem tailTrace_3665392 : CollatzResearch.WordTrace tailWord_3665392 prefixEnd_3665392 1882107883144828370643175 := by
  unfold tailWord_3665392
  simp only [CollatzResearch.WordTrace]
  refine ⟨66843914568459128980187215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89125219424612171973582953 66843914568459128980187215)
  ·
    refine ⟨100265871852688693470280823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66843914568459128980187215 100265871852688693470280823)
    ·
      refine ⟨150398807779033040205421235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100265871852688693470280823 150398807779033040205421235)
      ·
        refine ⟨225598211668549560308131853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150398807779033040205421235 225598211668549560308131853)
        ·
          refine ⟨84599329375706085115549445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225598211668549560308131853 84599329375706085115549445)
          ·
            refine ⟨15862374257944890959165521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84599329375706085115549445 15862374257944890959165521)
            ·
              refine ⟨11896780693458668219374141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15862374257944890959165521 11896780693458668219374141)
              ·
                refine ⟨4461292760047000582265303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11896780693458668219374141 4461292760047000582265303)
                ·
                  refine ⟨6691939140070500873397955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4461292760047000582265303 6691939140070500873397955)
                  ·
                    refine ⟨10037908710105751310096933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6691939140070500873397955 10037908710105751310096933)
                    ·
                      refine ⟨1882107883144828370643175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10037908710105751310096933 1882107883144828370643175)
                      ·
                        rfl

theorem cell23_3665392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 4].length) (baseStart_3665392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665392 prefixEnd_3665392 := by exact prefixLift 3665392
  have htrace : WordTrace (prefixWord ++ tailWord_3665392) baseStart_3665392 baseEnd_3665392 := by
    simpa [prefixWord, tailWord_3665392, baseEnd_3665392] using wordTrace_append hprefix tailTrace_3665392
  have hstable : (prefixWord ++ tailWord_3665392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665392).length < 2 ^ (prefixWord ++ tailWord_3665392).sum := by decide
  have hdescent : baseEnd_3665392 < baseStart_3665392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665402 : List Nat := [3, 1, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_3665402 : Nat := 118140960795 + 3665402 * 2 ^ 59
def prefixEnd_3665402 : Nat := 4983230072969 + 3 ^ 40 * 3665402 * 2
def baseEnd_3665402 : Nat := 627371005983791110506043

theorem tailTrace_3665402 : CollatzResearch.WordTrace tailWord_3665402 prefixEnd_3665402 627371005983791110506043 := by
  unfold tailWord_3665402
  simp only [CollatzResearch.WordTrace]
  refine ⟨33422048466720507417059615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89125462577921353112158973 33422048466720507417059615)
  ·
    refine ⟨50133072700080761125589423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33422048466720507417059615 50133072700080761125589423)
    ·
      refine ⟨75199609050121141688384135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50133072700080761125589423 75199609050121141688384135)
      ·
        refine ⟨112799413575181712532576203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75199609050121141688384135 112799413575181712532576203)
        ·
          refine ⟨169199120362772568798864305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112799413575181712532576203 169199120362772568798864305)
          ·
            refine ⟨126899340272079426599148229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169199120362772568798864305 126899340272079426599148229)
            ·
              refine ⟨23793626301014892487340293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126899340272079426599148229 23793626301014892487340293)
              ·
                refine ⟨4461304931440292341376305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23793626301014892487340293 4461304931440292341376305)
                ·
                  refine ⟨3345978698580219256032229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461304931440292341376305 3345978698580219256032229)
                  ·
                    refine ⟨627371005983791110506043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345978698580219256032229 627371005983791110506043)
                    ·
                      rfl

theorem cell23_3665402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_3665402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665402 prefixEnd_3665402 := by exact prefixLift 3665402
  have htrace : WordTrace (prefixWord ++ tailWord_3665402) baseStart_3665402 baseEnd_3665402 := by
    simpa [prefixWord, tailWord_3665402, baseEnd_3665402] using wordTrace_append hprefix tailTrace_3665402
  have hstable : (prefixWord ++ tailWord_3665402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665402).length < 2 ^ (prefixWord ++ tailWord_3665402).sum := by decide
  have hdescent : baseEnd_3665402 < baseStart_3665402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665405 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3665405 : Nat := 118140960795 + 3665405 * 2 ^ 59
def prefixEnd_3665405 : Nat := 4983230072969 + 3 ^ 40 * 3665405 * 2
def baseEnd_3665405 : Nat := 1882114558393336819780615

theorem tailTrace_3665405 : CollatzResearch.WordTrace tailWord_3665405 prefixEnd_3665405 1882114558393336819780615 := by
  unfold tailWord_3665405
  simp only [CollatzResearch.WordTrace]
  refine ⟨133688303285871161180597669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89125535523914107453731779 133688303285871161180597669)
  ·
    refine ⟨25066556866100842721362063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133688303285871161180597669 25066556866100842721362063)
    ·
      refine ⟨37599835299151264082043095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25066556866100842721362063 37599835299151264082043095)
      ·
        refine ⟨56399752948726896123064643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37599835299151264082043095 56399752948726896123064643)
        ·
          refine ⟨84599629423090344184596965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56399752948726896123064643 84599629423090344184596965)
          ·
            refine ⟨15862430516829439534611931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84599629423090344184596965 15862430516829439534611931)
            ·
              refine ⟨23793645775244159301917897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15862430516829439534611931 23793645775244159301917897)
              ·
                refine ⟨17845234331433119476438423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23793645775244159301917897 17845234331433119476438423)
                ·
                  refine ⟨26767851497149679214657635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17845234331433119476438423 26767851497149679214657635)
                  ·
                    refine ⟨40151777245724518821986453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26767851497149679214657635 40151777245724518821986453)
                    ·
                      refine ⟨1882114558393336819780615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40151777245724518821986453 1882114558393336819780615)
                      ·
                        rfl

theorem cell23_3665405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3665405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665405 prefixEnd_3665405 := by exact prefixLift 3665405
  have htrace : WordTrace (prefixWord ++ tailWord_3665405) baseStart_3665405 baseEnd_3665405 := by
    simpa [prefixWord, tailWord_3665405, baseEnd_3665405] using wordTrace_append hprefix tailTrace_3665405
  have hstable : (prefixWord ++ tailWord_3665405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665405).length < 2 ^ (prefixWord ++ tailWord_3665405).sum := by decide
  have hdescent : baseEnd_3665405 < baseStart_3665405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665415 : List Nat := [1, 1, 4, 3, 2, 1, 1, 10]
def baseStart_3665415 : Nat := 118140960795 + 3665415 * 2 ^ 59
def prefixEnd_3665415 : Nat := 4983230072969 + 3 ^ 40 * 3665415 * 2
def baseEnd_3665415 : Nat := 69708136785180806690947

theorem tailTrace_3665415 : CollatzResearch.WordTrace tailWord_3665415 prefixEnd_3665415 69708136785180806690947 := by
  unfold tailWord_3665415
  simp only [CollatzResearch.WordTrace]
  refine ⟨133688668015834932888461699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89125778677223288592307799 133688668015834932888461699)
  ·
    refine ⟨200533002023752399332692549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133688668015834932888461699 200533002023752399332692549)
    ·
      refine ⟨37599937879453574874879853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200533002023752399332692549 37599937879453574874879853)
      ·
        refine ⟨14099976704795090578079945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37599937879453574874879853 14099976704795090578079945)
        ·
          refine ⟨10574982528596317933559959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14099976704795090578079945 10574982528596317933559959)
          ·
            refine ⟨15862473792894476900339939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10574982528596317933559959 15862473792894476900339939)
            ·
              refine ⟨23793710689341715350509909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15862473792894476900339939 23793710689341715350509909)
              ·
                refine ⟨69708136785180806690947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23793710689341715350509909 69708136785180806690947)
                ·
                  rfl

theorem cell23_3665415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 10].length) (baseStart_3665415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665415 prefixEnd_3665415 := by exact prefixLift 3665415
  have htrace : WordTrace (prefixWord ++ tailWord_3665415) baseStart_3665415 baseEnd_3665415 := by
    simpa [prefixWord, tailWord_3665415, baseEnd_3665415] using wordTrace_append hprefix tailTrace_3665415
  have hstable : (prefixWord ++ tailWord_3665415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665415).length < 2 ^ (prefixWord ++ tailWord_3665415).sum := by decide
  have hdescent : baseEnd_3665415 < baseStart_3665415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665419 : List Nat := [1, 1, 1, 1, 8, 1, 1, 3, 2, 4]
def baseStart_3665419 : Nat := 118140960795 + 3665419 * 2 ^ 59
def prefixEnd_3665419 : Nat := 4983230072969 + 3 ^ 40 * 3665419 * 2
def baseEnd_3665419 : Nat := 627373915707499921668517

theorem tailTrace_3665419 : CollatzResearch.WordTrace tailWord_3665419 prefixEnd_3665419 627373915707499921668517 := by
  unfold tailWord_3665419
  simp only [CollatzResearch.WordTrace]
  refine ⟨133688813907820441571607311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89125875938546961047738207 133688813907820441571607311)
  ·
    refine ⟨200533220861730662357410967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133688813907820441571607311 200533220861730662357410967)
    ·
      refine ⟨300799831292595993536116451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200533220861730662357410967 300799831292595993536116451)
      ·
        refine ⟨451199746938893990304174677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300799831292595993536116451 451199746938893990304174677)
        ·
          refine ⟨5287497034440163948877047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 451199746938893990304174677 5287497034440163948877047)
          ·
            refine ⟨7931245551660245923315571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287497034440163948877047 7931245551660245923315571)
            ·
              refine ⟨11896868327490368884973357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7931245551660245923315571 11896868327490368884973357)
              ·
                refine ⟨4461325622808888331865009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11896868327490368884973357 4461325622808888331865009)
                ·
                  refine ⟨3345994217106666248898757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461325622808888331865009 3345994217106666248898757)
                  ·
                    refine ⟨627373915707499921668517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3345994217106666248898757 627373915707499921668517)
                    ·
                      rfl

theorem cell23_3665419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 4].length) (baseStart_3665419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665419 prefixEnd_3665419 := by exact prefixLift 3665419
  have htrace : WordTrace (prefixWord ++ tailWord_3665419) baseStart_3665419 baseEnd_3665419 := by
    simpa [prefixWord, tailWord_3665419, baseEnd_3665419] using wordTrace_append hprefix tailTrace_3665419
  have hstable : (prefixWord ++ tailWord_3665419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665419).length < 2 ^ (prefixWord ++ tailWord_3665419).sum := by decide
  have hdescent : baseEnd_3665419 < baseStart_3665419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665429 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 3]
def baseStart_3665429 : Nat := 118140960795 + 3665429 * 2 ^ 59
def prefixEnd_3665429 : Nat := 4983230072969 + 3 ^ 40 * 3665429 * 2
def baseEnd_3665429 : Nat := 1882126881929044725880505

theorem tailTrace_3665429 : CollatzResearch.WordTrace tailWord_3665429 prefixEnd_3665429 1882126881929044725880505 := by
  unfold tailWord_3665429
  simp only [CollatzResearch.WordTrace]
  refine ⟨133689178637784213279471341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89126119091856142186314227 133689178637784213279471341)
  ·
    refine ⟨50133441989169079979801753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133689178637784213279471341 50133441989169079979801753)
    ·
      refine ⟨37600081491876809984851315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50133441989169079979801753 37600081491876809984851315)
      ·
        refine ⟨56400122237815214977276973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37600081491876809984851315 56400122237815214977276973)
        ·
          refine ⟨21150045839180705616478865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56400122237815214977276973 21150045839180705616478865)
          ·
            refine ⟨15862534379385529212359149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21150045839180705616478865 15862534379385529212359149)
            ·
              refine ⟨5948450392269573454634681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15862534379385529212359149 5948450392269573454634681)
              ·
                refine ⟨4461337794202180090976011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5948450392269573454634681 4461337794202180090976011)
                ·
                  refine ⟨6692006691303270136464017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4461337794202180090976011 6692006691303270136464017)
                  ·
                    refine ⟨5019005018477452602348013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6692006691303270136464017 5019005018477452602348013)
                    ·
                      refine ⟨1882126881929044725880505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5019005018477452602348013 1882126881929044725880505)
                      ·
                        rfl

theorem cell23_3665429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_3665429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665429 prefixEnd_3665429 := by exact prefixLift 3665429
  have htrace : WordTrace (prefixWord ++ tailWord_3665429) baseStart_3665429 baseEnd_3665429 := by
    simpa [prefixWord, tailWord_3665429, baseEnd_3665429] using wordTrace_append hprefix tailTrace_3665429
  have hstable : (prefixWord ++ tailWord_3665429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665429).length < 2 ^ (prefixWord ++ tailWord_3665429).sum := by decide
  have hdescent : baseEnd_3665429 < baseStart_3665429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665442 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_3665442 : Nat := 118140960795 + 3665442 * 2 ^ 59
def prefixEnd_3665442 : Nat := 4983230072969 + 3 ^ 40 * 3665442 * 2
def baseEnd_3665442 : Nat := 1882133557177553175017945

theorem tailTrace_3665442 : CollatzResearch.WordTrace tailWord_3665442 prefixEnd_3665442 1882133557177553175017945 := by
  unfold tailWord_3665442
  simp only [CollatzResearch.WordTrace]
  refine ⟨33422413196684279124923645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89126435191158077666463053 33422413196684279124923645)
  ·
    refine ⟨12533404948756604671846367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33422413196684279124923645 12533404948756604671846367)
    ·
      refine ⟨18800107423134907007769551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12533404948756604671846367 18800107423134907007769551)
      ·
        refine ⟨28200161134702360511654327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18800107423134907007769551 28200161134702360511654327)
        ·
          refine ⟨42300241702053540767481491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28200161134702360511654327 42300241702053540767481491)
          ·
            refine ⟨63450362553080311151222237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42300241702053540767481491 63450362553080311151222237)
            ·
              refine ⟨23793885957405116681708339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63450362553080311151222237 23793885957405116681708339)
              ·
                refine ⟨35690828936107675022562509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23793885957405116681708339 35690828936107675022562509)
                ·
                  refine ⟨13384060851040378133460941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35690828936107675022562509 13384060851040378133460941)
                  ·
                    refine ⟨5019022819140141800047853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13384060851040378133460941 5019022819140141800047853)
                    ·
                      refine ⟨1882133557177553175017945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5019022819140141800047853 1882133557177553175017945)
                      ·
                        rfl

theorem cell23_3665442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_3665442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665442 prefixEnd_3665442 := by exact prefixLift 3665442
  have htrace : WordTrace (prefixWord ++ tailWord_3665442) baseStart_3665442 baseEnd_3665442 := by
    simpa [prefixWord, tailWord_3665442, baseEnd_3665442] using wordTrace_append hprefix tailTrace_3665442
  have hstable : (prefixWord ++ tailWord_3665442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665442).length < 2 ^ (prefixWord ++ tailWord_3665442).sum := by decide
  have hdescent : baseEnd_3665442 < baseStart_3665442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665459 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 3]
def baseStart_3665459 : Nat := 118140960795 + 3665459 * 2 ^ 59
def prefixEnd_3665459 : Nat := 4983230072969 + 3 ^ 40 * 3665459 * 2
def baseEnd_3665459 : Nat := 1882142286348679608505367

theorem tailTrace_3665459 : CollatzResearch.WordTrace tailWord_3665459 prefixEnd_3665459 1882142286348679608505367 := by
  unfold tailWord_3665459
  simp only [CollatzResearch.WordTrace]
  refine ⟨133690272827675528403063431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89126848551783685602042287 133690272827675528403063431)
  ·
    refine ⟨200535409241513292604595147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133690272827675528403063431 200535409241513292604595147)
    ·
      refine ⟨300803113862269938906892721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200535409241513292604595147 300803113862269938906892721)
      ·
        refine ⟨225602335396702454180169541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300803113862269938906892721 225602335396702454180169541)
        ·
          refine ⟨42300437886881710158781789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225602335396702454180169541 42300437886881710158781789)
          ·
            refine ⟨15862664207580641309543171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42300437886881710158781789 15862664207580641309543171)
            ·
              refine ⟨23793996311370961964314757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15862664207580641309543171 23793996311370961964314757)
              ·
                refine ⟨4461374308382055368309017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23793996311370961964314757 4461374308382055368309017)
                ·
                  refine ⟨3346030731286541526231763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461374308382055368309017 3346030731286541526231763)
                  ·
                    refine ⟨5019046096929812289347645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3346030731286541526231763 5019046096929812289347645)
                    ·
                      refine ⟨1882142286348679608505367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5019046096929812289347645 1882142286348679608505367)
                      ·
                        rfl

theorem cell23_3665459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 1, 3].length) (baseStart_3665459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665459 prefixEnd_3665459 := by exact prefixLift 3665459
  have htrace : WordTrace (prefixWord ++ tailWord_3665459) baseStart_3665459 baseEnd_3665459 := by
    simpa [prefixWord, tailWord_3665459, baseEnd_3665459] using wordTrace_append hprefix tailTrace_3665459
  have hstable : (prefixWord ++ tailWord_3665459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665459).length < 2 ^ (prefixWord ++ tailWord_3665459).sum := by decide
  have hdescent : baseEnd_3665459 < baseStart_3665459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665494 : List Nat := [5, 2, 2, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_3665494 : Nat := 118140960795 + 3665494 * 2 ^ 59
def prefixEnd_3665494 : Nat := 4983230072969 + 3 ^ 40 * 3665494 * 2
def baseEnd_3665494 : Nat := 1882160258171586971567707

theorem tailTrace_3665494 : CollatzResearch.WordTrace tailWord_3665494 prefixEnd_3665494 1882160258171586971567707 := by
  unfold tailWord_3665494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8355721836409295586286721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89127699588365819587058357 8355721836409295586286721)
  ·
    refine ⟨6266791377306971689715041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8355721836409295586286721 6266791377306971689715041)
    ·
      refine ⟨4700093532980228767286281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6266791377306971689715041 4700093532980228767286281)
      ·
        refine ⟨3525070149735171575464711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4700093532980228767286281 3525070149735171575464711)
        ·
          refine ⟨5287605224602757363197067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525070149735171575464711 5287605224602757363197067)
          ·
            refine ⟨7931407836904136044795601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287605224602757363197067 7931407836904136044795601)
            ·
              refine ⟨5948555877678102033596701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7931407836904136044795601 5948555877678102033596701)
              ·
                refine ⟨2230708454129288262598763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5948555877678102033596701 2230708454129288262598763)
                ·
                  refine ⟨3346062681193932393898145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230708454129288262598763 3346062681193932393898145)
                  ·
                    refine ⟨2509547010895449295423609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3346062681193932393898145 2509547010895449295423609)
                    ·
                      refine ⟨1882160258171586971567707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509547010895449295423609 1882160258171586971567707)
                      ·
                        rfl

theorem cell23_3665494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_3665494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665494 prefixEnd_3665494 := by exact prefixLift 3665494
  have htrace : WordTrace (prefixWord ++ tailWord_3665494) baseStart_3665494 baseEnd_3665494 := by
    simpa [prefixWord, tailWord_3665494, baseEnd_3665494] using wordTrace_append hprefix tailTrace_3665494
  have hstable : (prefixWord ++ tailWord_3665494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665494).length < 2 ^ (prefixWord ++ tailWord_3665494).sum := by decide
  have hdescent : baseEnd_3665494 < baseStart_3665494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665505 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 9]
def baseStart_3665505 : Nat := 118140960795 + 3665505 * 2 ^ 59
def prefixEnd_3665505 : Nat := 4983230072969 + 3 ^ 40 * 3665505 * 2
def baseEnd_3665505 : Nat := 209129545162087380947795

theorem tailTrace_3665505 : CollatzResearch.WordTrace tailWord_3665505 prefixEnd_3665505 209129545162087380947795 := by
  unfold tailWord_3665505
  simp only [CollatzResearch.WordTrace]
  refine ⟨133691950585508878259237969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89127967057005918839491979 133691950585508878259237969)
  ·
    refine ⟨100268962939131658694428477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133691950585508878259237969 100268962939131658694428477)
    ·
      refine ⟨37600861102174372010410679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100268962939131658694428477 37600861102174372010410679)
      ·
        refine ⟨56401291653261558015616019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37600861102174372010410679 56401291653261558015616019)
        ·
          refine ⟨84601937479892337023424029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56401291653261558015616019 84601937479892337023424029)
          ·
            refine ⟨31725726554959626383784011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84601937479892337023424029 31725726554959626383784011)
            ·
              refine ⟨47588589832439439575676017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31725726554959626383784011 47588589832439439575676017)
              ·
                refine ⟨35691442374329579681757013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47588589832439439575676017 35691442374329579681757013)
                ·
                  refine ⟨209129545162087380947795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35691442374329579681757013 209129545162087380947795)
                  ·
                    rfl

theorem cell23_3665505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 9].length) (baseStart_3665505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665505 prefixEnd_3665505 := by exact prefixLift 3665505
  have htrace : WordTrace (prefixWord ++ tailWord_3665505) baseStart_3665505 baseEnd_3665505 := by
    simpa [prefixWord, tailWord_3665505, baseEnd_3665505] using wordTrace_append hprefix tailTrace_3665505
  have hstable : (prefixWord ++ tailWord_3665505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665505).length < 2 ^ (prefixWord ++ tailWord_3665505).sum := by decide
  have hdescent : baseEnd_3665505 < baseStart_3665505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665522 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 7]
def baseStart_3665522 : Nat := 118140960795 + 3665522 * 2 ^ 59
def prefixEnd_3665522 : Nat := 4983230072969 + 3 ^ 40 * 3665522 * 2
def baseEnd_3665522 : Nat := 209130515069990318001953

theorem tailTrace_3665522 : CollatzResearch.WordTrace tailWord_3665522 prefixEnd_3665522 209130515069990318001953 := by
  unfold tailWord_3665522
  simp only [CollatzResearch.WordTrace]
  refine ⟨33423142656611822540651705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89128380417631526775071213 33423142656611822540651705)
  ·
    refine ⟨25067356992458866905488779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33423142656611822540651705 25067356992458866905488779)
    ·
      refine ⟨37601035488688300358233169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25067356992458866905488779 37601035488688300358233169)
      ·
        refine ⟨28200776616516225268674877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37601035488688300358233169 28200776616516225268674877)
        ·
          refine ⟨10575291231193584475753079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28200776616516225268674877 10575291231193584475753079)
          ·
            refine ⟨15862936846790376713629619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10575291231193584475753079 15862936846790376713629619)
            ·
              refine ⟨23794405270185565070444429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15862936846790376713629619 23794405270185565070444429)
              ·
                refine ⟨8922901976319586901416661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23794405270185565070444429 8922901976319586901416661)
                ·
                  refine ⟨209130515069990318001953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8922901976319586901416661 209130515069990318001953)
                  ·
                    rfl

theorem cell23_3665522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_3665522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665522 prefixEnd_3665522 := by exact prefixLift 3665522
  have htrace : WordTrace (prefixWord ++ tailWord_3665522) baseStart_3665522 baseEnd_3665522 := by
    simpa [prefixWord, tailWord_3665522, baseEnd_3665522] using wordTrace_append hprefix tailTrace_3665522
  have hstable : (prefixWord ++ tailWord_3665522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665522).length < 2 ^ (prefixWord ++ tailWord_3665522).sum := by decide
  have hdescent : baseEnd_3665522 < baseStart_3665522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665569 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 2, 5]
def baseStart_3665569 : Nat := 118140960795 + 3665569 * 2 ^ 59
def prefixEnd_3665569 : Nat := 4983230072969 + 3 ^ 40 * 3665569 * 2
def baseEnd_3665569 : Nat := 627399589740224726043287

theorem tailTrace_3665569 : CollatzResearch.WordTrace tailWord_3665569 prefixEnd_3665569 627399589740224726043287 := by
  unfold tailWord_3665569
  simp only [CollatzResearch.WordTrace]
  refine ⟨133694284857277017189567761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89129523238184678126378507 133694284857277017189567761)
  ·
    refine ⟨100270713642957762892175821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133694284857277017189567761 100270713642957762892175821)
    ·
      refine ⟨37601517616109161084565933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100270713642957762892175821 37601517616109161084565933)
      ·
        refine ⟨14100569106040935406712225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37601517616109161084565933 14100569106040935406712225)
        ·
          refine ⟨10575426829530701555034169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14100569106040935406712225 10575426829530701555034169)
          ·
            refine ⟨7931570122148026166275627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10575426829530701555034169 7931570122148026166275627)
            ·
              refine ⟨11897355183222039249413441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7931570122148026166275627 11897355183222039249413441)
              ·
                refine ⟨8923016387416529437060081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11897355183222039249413441 8923016387416529437060081)
                ·
                  refine ⟨6692262290562397077795061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8923016387416529437060081 6692262290562397077795061)
                  ·
                    refine ⟨627399589740224726043287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6692262290562397077795061 627399589740224726043287)
                    ·
                      rfl

theorem cell23_3665569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_3665569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665569 prefixEnd_3665569 := by exact prefixLift 3665569
  have htrace : WordTrace (prefixWord ++ tailWord_3665569) baseStart_3665569 baseEnd_3665569 := by
    simpa [prefixWord, tailWord_3665569, baseEnd_3665569] using wordTrace_append hprefix tailTrace_3665569
  have hstable : (prefixWord ++ tailWord_3665569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665569).length < 2 ^ (prefixWord ++ tailWord_3665569).sum := by decide
  have hdescent : baseEnd_3665569 < baseStart_3665569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665592 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_3665592 : Nat := 118140960795 + 3665592 * 2 ^ 59
def prefixEnd_3665592 : Nat := 4983230072969 + 3 ^ 40 * 3665592 * 2
def baseEnd_3665592 : Nat := 1882210579275727588142255

theorem tailTrace_3665592 : CollatzResearch.WordTrace tailWord_3665592 prefixEnd_3665592 1882210579275727588142255 := by
  unfold tailWord_3665592
  simp only [CollatzResearch.WordTrace]
  refine ⟨66847561868096846058827515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89130082490795794745103353 66847561868096846058827515)
  ·
    refine ⟨100271342802145269088241273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66847561868096846058827515 100271342802145269088241273)
    ·
      refine ⟨75203507101608951816180955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100271342802145269088241273 75203507101608951816180955)
      ·
        refine ⟨112805260652413427724271433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75203507101608951816180955 112805260652413427724271433)
        ·
          refine ⟨84603945489310070793203575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112805260652413427724271433 84603945489310070793203575)
          ·
            refine ⟨126905918233965106189805363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84603945489310070793203575 126905918233965106189805363)
            ·
              refine ⟨190358877350947659284708045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126905918233965106189805363 190358877350947659284708045)
              ·
                refine ⟨71384579006605372231765517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190358877350947659284708045 71384579006605372231765517)
                ·
                  refine ⟨26769217127477014586912069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71384579006605372231765517 26769217127477014586912069)
                  ·
                    refine ⟨5019228211401940235046013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26769217127477014586912069 5019228211401940235046013)
                    ·
                      refine ⟨1882210579275727588142255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5019228211401940235046013 1882210579275727588142255)
                      ·
                        rfl

theorem cell23_3665592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_3665592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665592 prefixEnd_3665592 := by exact prefixLift 3665592
  have htrace : WordTrace (prefixWord ++ tailWord_3665592) baseStart_3665592 baseEnd_3665592 := by
    simpa [prefixWord, tailWord_3665592, baseEnd_3665592] using wordTrace_append hprefix tailTrace_3665592
  have hstable : (prefixWord ++ tailWord_3665592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665592).length < 2 ^ (prefixWord ++ tailWord_3665592).sum := by decide
  have hdescent : baseEnd_3665592 < baseStart_3665592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665633 : List Nat := [1, 2, 3, 1, 5, 1, 1, 4, 1, 4]
def baseStart_3665633 : Nat := 118140960795 + 3665633 * 2 ^ 59
def prefixEnd_3665633 : Nat := 4983230072969 + 3 ^ 40 * 3665633 * 2
def baseEnd_3665633 : Nat := 627410543994187309243189

theorem tailTrace_3665633 : CollatzResearch.WordTrace tailWord_3665633 prefixEnd_3665633 627410543994187309243189 := by
  unfold tailWord_3665633
  simp only [CollatzResearch.WordTrace]
  refine ⟨133696619129045156119897553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89131079419363437413265035 133696619129045156119897553)
  ·
    refine ⟨100272464346783867089923165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133696619129045156119897553 100272464346783867089923165)
    ·
      refine ⟨37602174130043950158721187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100272464346783867089923165 37602174130043950158721187)
      ·
        refine ⟨56403261195065925238081781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37602174130043950158721187 56403261195065925238081781)
        ·
          refine ⟨5287805737037430491070167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56403261195065925238081781 5287805737037430491070167)
          ·
            refine ⟨7931708605556145736605251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287805737037430491070167 7931708605556145736605251)
            ·
              refine ⟨11897562908334218604907877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7931708605556145736605251 11897562908334218604907877)
              ·
                refine ⟨2230793045312665988420227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11897562908334218604907877 2230793045312665988420227)
                ·
                  refine ⟨3346189567968998982630341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230793045312665988420227 3346189567968998982630341)
                  ·
                    refine ⟨627410543994187309243189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3346189567968998982630341 627410543994187309243189)
                    ·
                      rfl

theorem cell23_3665633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_3665633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665633 prefixEnd_3665633 := by exact prefixLift 3665633
  have htrace : WordTrace (prefixWord ++ tailWord_3665633) baseStart_3665633 baseEnd_3665633 := by
    simpa [prefixWord, tailWord_3665633, baseEnd_3665633] using wordTrace_append hprefix tailTrace_3665633
  have hstable : (prefixWord ++ tailWord_3665633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665633).length < 2 ^ (prefixWord ++ tailWord_3665633).sum := by decide
  have hdescent : baseEnd_3665633 < baseStart_3665633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665676 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_3665676 : Nat := 118140960795 + 3665676 * 2 ^ 59
def prefixEnd_3665676 : Nat := 4983230072969 + 3 ^ 40 * 3665676 * 2
def baseEnd_3665676 : Nat := 627417903883568419830623

theorem tailTrace_3665676 : CollatzResearch.WordTrace tailWord_3665676 prefixEnd_3665676 627417903883568419830623 := by
  unfold tailWord_3665676
  simp only [CollatzResearch.WordTrace]
  refine ⟨66849093733944687231856441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89132124978592916309141921 66849093733944687231856441)
  ·
    refine ⟨50136820300458515423892331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66849093733944687231856441 50136820300458515423892331)
    ·
      refine ⟨75205230450687773135838497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50136820300458515423892331 75205230450687773135838497)
      ·
        refine ⟨56403922838015829851878873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75205230450687773135838497 56403922838015829851878873)
        ·
          refine ⟨42302942128511872388909155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56403922838015829851878873 42302942128511872388909155)
          ·
            refine ⟨63454413192767808583363733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42302942128511872388909155 63454413192767808583363733)
            ·
              refine ⟨2974425618410991027345175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63454413192767808583363733 2974425618410991027345175)
              ·
                refine ⟨4461638427616486541017763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974425618410991027345175 4461638427616486541017763)
                ·
                  refine ⟨6692457641424729811526645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4461638427616486541017763 6692457641424729811526645)
                  ·
                    refine ⟨627417903883568419830623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6692457641424729811526645 627417903883568419830623)
                    ·
                      rfl

theorem cell23_3665676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_3665676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665676 prefixEnd_3665676 := by exact prefixLift 3665676
  have htrace : WordTrace (prefixWord ++ tailWord_3665676) baseStart_3665676 baseEnd_3665676 := by
    simpa [prefixWord, tailWord_3665676, baseEnd_3665676] using wordTrace_append hprefix tailTrace_3665676
  have hstable : (prefixWord ++ tailWord_3665676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665676).length < 2 ^ (prefixWord ++ tailWord_3665676).sum := by decide
  have hdescent : baseEnd_3665676 < baseStart_3665676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665699 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 3]
def baseStart_3665699 : Nat := 118140960795 + 3665699 * 2 ^ 59
def prefixEnd_3665699 : Nat := 4983230072969 + 3 ^ 40 * 3665699 * 2
def baseEnd_3665699 : Nat := 1882265521705758669504263

theorem tailTrace_3665699 : CollatzResearch.WordTrace tailWord_3665699 prefixEnd_3665699 1882265521705758669504263 := by
  unfold tailWord_3665699
  simp only [CollatzResearch.WordTrace]
  refine ⟨133699026346806049391800151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89132684231204032927866767 133699026346806049391800151)
  ·
    refine ⟨200548539520209074087700227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133699026346806049391800151 200548539520209074087700227)
    ·
      refine ⟨300822809280313611131550341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200548539520209074087700227 300822809280313611131550341)
      ·
        refine ⟨56404276740058802087165689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300822809280313611131550341 56404276740058802087165689)
        ·
          refine ⟨42303207555044101565374267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56404276740058802087165689 42303207555044101565374267)
          ·
            refine ⟨63454811332566152348061401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42303207555044101565374267 63454811332566152348061401)
            ·
              refine ⟨47591108499424614261046051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63454811332566152348061401 47591108499424614261046051)
              ·
                refine ⟨71386662749136921391569077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47591108499424614261046051 71386662749136921391569077)
                ·
                  refine ⟨6692499632731586380459601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71386662749136921391569077 6692499632731586380459601)
                  ·
                    refine ⟨5019374724548689785344701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6692499632731586380459601 5019374724548689785344701)
                    ·
                      refine ⟨1882265521705758669504263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5019374724548689785344701 1882265521705758669504263)
                      ·
                        rfl

theorem cell23_3665699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_3665699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665699 prefixEnd_3665699 := by exact prefixLift 3665699
  have htrace : WordTrace (prefixWord ++ tailWord_3665699) baseStart_3665699 baseEnd_3665699 := by
    simpa [prefixWord, tailWord_3665699, baseEnd_3665699] using wordTrace_append hprefix tailTrace_3665699
  have hstable : (prefixWord ++ tailWord_3665699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665699).length < 2 ^ (prefixWord ++ tailWord_3665699).sum := by decide
  have hdescent : baseEnd_3665699 < baseStart_3665699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665713 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 3, 2, 2]
def baseStart_3665713 : Nat := 118140960795 + 3665713 * 2 ^ 59
def prefixEnd_3665713 : Nat := 4983230072969 + 3 ^ 40 * 3665713 * 2
def baseEnd_3665713 : Nat := 1882272710434921614729199

theorem tailTrace_3665713 : CollatzResearch.WordTrace tailWord_3665713 prefixEnd_3665713 1882272710434921614729199 := by
  unfold tailWord_3665713
  simp only [CollatzResearch.WordTrace]
  refine ⟨133699536968755329782809793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89133024645836886521873195 133699536968755329782809793)
  ·
    refine ⟨100274652726566497337107345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133699536968755329782809793 100274652726566497337107345)
    ·
      refine ⟨75205989544924873002830509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100274652726566497337107345 75205989544924873002830509)
      ·
        refine ⟨28202246079346827376061441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75205989544924873002830509 28202246079346827376061441)
        ·
          refine ⟨21151684559510120532046081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28202246079346827376061441 21151684559510120532046081)
          ·
            refine ⟨15863763419632590399034561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21151684559510120532046081 15863763419632590399034561)
            ·
              refine ⟨11897822564724442799275921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15863763419632590399034561 11897822564724442799275921)
              ·
                refine ⟨8923366923543332099456941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11897822564724442799275921 8923366923543332099456941)
                ·
                  refine ⟨3346262596328749537296353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8923366923543332099456941 3346262596328749537296353)
                  ·
                    refine ⟨2509696947246562152972265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3346262596328749537296353 2509696947246562152972265)
                    ·
                      refine ⟨1882272710434921614729199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509696947246562152972265 1882272710434921614729199)
                      ·
                        rfl

theorem cell23_3665713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_3665713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665713 prefixEnd_3665713 := by exact prefixLift 3665713
  have htrace : WordTrace (prefixWord ++ tailWord_3665713) baseStart_3665713 baseEnd_3665713 := by
    simpa [prefixWord, tailWord_3665713, baseEnd_3665713] using wordTrace_append hprefix tailTrace_3665713
  have hstable : (prefixWord ++ tailWord_3665713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665713).length < 2 ^ (prefixWord ++ tailWord_3665713).sum := by decide
  have hdescent : baseEnd_3665713 < baseStart_3665713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665786 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2]
def baseStart_3665786 : Nat := 118140960795 + 3665786 * 2 ^ 59
def prefixEnd_3665786 : Nat := 4983230072969 + 3 ^ 40 * 3665786 * 2
def baseEnd_3665786 : Nat := 1882310194522699829116363

theorem tailTrace_3665786 : CollatzResearch.WordTrace tailWord_3665786 prefixEnd_3665786 1882310194522699829116363 := by
  unfold tailWord_3665786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33425549874372715812554303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89134799664993908833478141 33425549874372715812554303)
  ·
    refine ⟨50138324811559073718831455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33425549874372715812554303 50138324811559073718831455)
    ·
      refine ⟨75207487217338610578247183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50138324811559073718831455 75207487217338610578247183)
      ·
        refine ⟨112811230826007915867370775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75207487217338610578247183 112811230826007915867370775)
        ·
          refine ⟨169216846239011873801056163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112811230826007915867370775 169216846239011873801056163)
          ·
            refine ⟨253825269358517810701584245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169216846239011873801056163 253825269358517810701584245)
            ·
              refine ⟨23796119002361044753273523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253825269358517810701584245 23796119002361044753273523)
              ·
                refine ⟨35694178503541567129910285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23796119002361044753273523 35694178503541567129910285)
                ·
                  refine ⟨13385316938828087673716357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35694178503541567129910285 13385316938828087673716357)
                  ·
                    refine ⟨2509746926030266438821817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13385316938828087673716357 2509746926030266438821817)
                    ·
                      refine ⟨1882310194522699829116363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509746926030266438821817 1882310194522699829116363)
                      ·
                        rfl

theorem cell23_3665786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_3665786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665786 prefixEnd_3665786 := by exact prefixLift 3665786
  have htrace : WordTrace (prefixWord ++ tailWord_3665786) baseStart_3665786 baseEnd_3665786 := by
    simpa [prefixWord, tailWord_3665786, baseEnd_3665786] using wordTrace_append hprefix tailTrace_3665786
  have hstable : (prefixWord ++ tailWord_3665786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665786).length < 2 ^ (prefixWord ++ tailWord_3665786).sum := by decide
  have hdescent : baseEnd_3665786 < baseStart_3665786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665820 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3665820 : Nat := 118140960795 + 3665820 * 2 ^ 59
def prefixEnd_3665820 : Nat := 4983230072969 + 3 ^ 40 * 3665820 * 2
def baseEnd_3665820 : Nat := 1882327652864952696091207

theorem tailTrace_3665820 : CollatzResearch.WordTrace tailWord_3665820 prefixEnd_3665820 1882327652864952696091207 := by
  unfold tailWord_3665820
  simp only [CollatzResearch.WordTrace]
  refine ⟨66851719789683843528477457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89135626386245124704636609 66851719789683843528477457)
  ·
    refine ⟨50138789842262882646358093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66851719789683843528477457 50138789842262882646358093)
    ·
      refine ⟨18802046190848580992384285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50138789842262882646358093 18802046190848580992384285)
      ·
        refine ⟨7050767321568217872144107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18802046190848580992384285 7050767321568217872144107)
        ·
          refine ⟨10576150982352326808216161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7050767321568217872144107 10576150982352326808216161)
          ·
            refine ⟨7932113236764245106162121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10576150982352326808216161 7932113236764245106162121)
            ·
              refine ⟨5949084927573183829621591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7932113236764245106162121 5949084927573183829621591)
              ·
                refine ⟨8923627391359775744432387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5949084927573183829621591 8923627391359775744432387)
                ·
                  refine ⟨13385441087039663616648581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8923627391359775744432387 13385441087039663616648581)
                  ·
                    refine ⟨2509770203819936928121609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13385441087039663616648581 2509770203819936928121609)
                    ·
                      refine ⟨1882327652864952696091207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509770203819936928121609 1882327652864952696091207)
                      ·
                        rfl

theorem cell23_3665820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3665820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665820 prefixEnd_3665820 := by exact prefixLift 3665820
  have htrace : WordTrace (prefixWord ++ tailWord_3665820) baseStart_3665820 baseEnd_3665820 := by
    simpa [prefixWord, tailWord_3665820, baseEnd_3665820] using wordTrace_append hprefix tailTrace_3665820
  have hstable : (prefixWord ++ tailWord_3665820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665820).length < 2 ^ (prefixWord ++ tailWord_3665820).sum := by decide
  have hdescent : baseEnd_3665820 < baseStart_3665820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665839 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 1, 7]
def baseStart_3665839 : Nat := 118140960795 + 3665839 * 2 ^ 59
def prefixEnd_3665839 : Nat := 4983230072969 + 3 ^ 40 * 3665839 * 2
def baseEnd_3665839 : Nat := 627445802999129373917873

theorem tailTrace_3665839 : CollatzResearch.WordTrace tailWord_3665839 prefixEnd_3665839 627445802999129373917873 := by
  unfold tailWord_3665839
  simp only [CollatzResearch.WordTrace]
  refine ⟨133704132566298853301896571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89136088377532568867931047 133704132566298853301896571)
  ·
    refine ⟨200556198849448279952844857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133704132566298853301896571 200556198849448279952844857)
    ·
      refine ⟨150417149137086209964633643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200556198849448279952844857 150417149137086209964633643)
      ·
        refine ⟨225625723705629314946950465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150417149137086209964633643 225625723705629314946950465)
        ·
          refine ⟨169219292779221986210212849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225625723705629314946950465 169219292779221986210212849)
          ·
            refine ⟨126914469584416489657659637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169219292779221986210212849 126914469584416489657659637)
            ·
              refine ⟨11898231523539045905405591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126914469584416489657659637 11898231523539045905405591)
              ·
                refine ⟨17847347285308568858108387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11898231523539045905405591 17847347285308568858108387)
                ·
                  refine ⟨26771020927962853287162581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17847347285308568858108387 26771020927962853287162581)
                  ·
                    refine ⟨627445802999129373917873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26771020927962853287162581 627445802999129373917873)
                    ·
                      rfl

theorem cell23_3665839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 7].length) (baseStart_3665839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665839 prefixEnd_3665839 := by exact prefixLift 3665839
  have htrace : WordTrace (prefixWord ++ tailWord_3665839) baseStart_3665839 baseEnd_3665839 := by
    simpa [prefixWord, tailWord_3665839, baseEnd_3665839] using wordTrace_append hprefix tailTrace_3665839
  have hstable : (prefixWord ++ tailWord_3665839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665839).length < 2 ^ (prefixWord ++ tailWord_3665839).sum := by decide
  have hdescent : baseEnd_3665839 < baseStart_3665839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665859 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 4]
def baseStart_3665859 : Nat := 118140960795 + 3665859 * 2 ^ 59
def prefixEnd_3665859 : Nat := 4983230072969 + 3 ^ 40 * 3665859 * 2
def baseEnd_3665859 : Nat := 1882347678610478043503527

theorem tailTrace_3665859 : CollatzResearch.WordTrace tailWord_3665859 prefixEnd_3665859 1882347678610478043503527 := by
  unfold tailWord_3665859
  simp only [CollatzResearch.WordTrace]
  refine ⟨133704862026226396717624631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89136574684150931145083087 133704862026226396717624631)
  ·
    refine ⟨200557293039339595076436947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133704862026226396717624631 200557293039339595076436947)
    ·
      refine ⟨300835939559009392614655421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200557293039339595076436947 300835939559009392614655421)
      ·
        refine ⟨112813477334628522230495783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300835939559009392614655421 112813477334628522230495783)
        ·
          refine ⟨169220216001942783345743675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112813477334628522230495783 169220216001942783345743675)
          ·
            refine ⟨253830324002914175018615513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169220216001942783345743675 253830324002914175018615513)
            ·
              refine ⟨190372743002185631263961635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253830324002914175018615513 190372743002185631263961635)
              ·
                refine ⟨285559114503278446895942453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190372743002185631263961635 285559114503278446895942453)
                ·
                  refine ⟨26771166984682354396494605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285559114503278446895942453 26771166984682354396494605)
                  ·
                    refine ⟨10039187619255882898685477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26771166984682354396494605 10039187619255882898685477)
                    ·
                      refine ⟨1882347678610478043503527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10039187619255882898685477 1882347678610478043503527)
                      ·
                        rfl

theorem cell23_3665859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_3665859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665859 prefixEnd_3665859 := by exact prefixLift 3665859
  have htrace : WordTrace (prefixWord ++ tailWord_3665859) baseStart_3665859 baseEnd_3665859 := by
    simpa [prefixWord, tailWord_3665859, baseEnd_3665859] using wordTrace_append hprefix tailTrace_3665859
  have hstable : (prefixWord ++ tailWord_3665859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665859).length < 2 ^ (prefixWord ++ tailWord_3665859).sum := by decide
  have hdescent : baseEnd_3665859 < baseStart_3665859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665876 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3665876 : Nat := 118140960795 + 3665876 * 2 ^ 59
def prefixEnd_3665876 : Nat := 4983230072969 + 3 ^ 40 * 3665876 * 2
def baseEnd_3665876 : Nat := 1882356407781604476990949

theorem tailTrace_3665876 : CollatzResearch.WordTrace tailWord_3665876 prefixEnd_3665876 1882356407781604476990949 := by
  unfold tailWord_3665876
  simp only [CollatzResearch.WordTrace]
  refine ⟨66852741033582404310496741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89136988044776539080662321 66852741033582404310496741)
  ·
    refine ⟨12534888943796700808218139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66852741033582404310496741 12534888943796700808218139)
    ·
      refine ⟨18802333415695051212327209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12534888943796700808218139 18802333415695051212327209)
      ·
        refine ⟨14101750061771288409245407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18802333415695051212327209 14101750061771288409245407)
        ·
          refine ⟨21152625092656932613868111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14101750061771288409245407 21152625092656932613868111)
          ·
            refine ⟨31728937638985398920802167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21152625092656932613868111 31728937638985398920802167)
            ·
              refine ⟨47593406458478098381203251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31728937638985398920802167 47593406458478098381203251)
              ·
                refine ⟨71390109687717147571804877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47593406458478098381203251 71390109687717147571804877)
                ·
                  refine ⟨26771291132893930339426829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71390109687717147571804877 26771291132893930339426829)
                  ·
                    refine ⟨10039234174835223877285061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26771291132893930339426829 10039234174835223877285061)
                    ·
                      refine ⟨1882356407781604476990949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10039234174835223877285061 1882356407781604476990949)
                      ·
                        rfl

theorem cell23_3665876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3665876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665876 prefixEnd_3665876 := by exact prefixLift 3665876
  have htrace : WordTrace (prefixWord ++ tailWord_3665876) baseStart_3665876 baseEnd_3665876 := by
    simpa [prefixWord, tailWord_3665876, baseEnd_3665876] using wordTrace_append hprefix tailTrace_3665876
  have hstable : (prefixWord ++ tailWord_3665876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665876).length < 2 ^ (prefixWord ++ tailWord_3665876).sum := by decide
  have hdescent : baseEnd_3665876 < baseStart_3665876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665910 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3665910 : Nat := 118140960795 + 3665910 * 2 ^ 59
def prefixEnd_3665910 : Nat := 4983230072969 + 3 ^ 40 * 3665910 * 2
def baseEnd_3665910 : Nat := 1882373866123857343965793

theorem tailTrace_3665910 : CollatzResearch.WordTrace tailWord_3665910 prefixEnd_3665910 1882373866123857343965793 := by
  unfold tailWord_3665910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8356670134315102026733199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89137814766027754951820789 8356670134315102026733199)
  ·
    refine ⟨12535005201472653040099799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8356670134315102026733199 12535005201472653040099799)
    ·
      refine ⟨18802507802208979560149699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12535005201472653040099799 18802507802208979560149699)
      ·
        refine ⟨28203761703313469340224549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18802507802208979560149699 28203761703313469340224549)
        ·
          refine ⟨5288205319371275501292103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28203761703313469340224549 5288205319371275501292103)
          ·
            refine ⟨7932307979056913251938155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288205319371275501292103 7932307979056913251938155)
            ·
              refine ⟨11898461968585369877907233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932307979056913251938155 11898461968585369877907233)
              ·
                refine ⟨8923846476439027408430425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11898461968585369877907233 8923846476439027408430425)
                ·
                  refine ⟨6692884857329270556322819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8923846476439027408430425 6692884857329270556322819)
                  ·
                    refine ⟨10039327285993905834484229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6692884857329270556322819 10039327285993905834484229)
                    ·
                      refine ⟨1882373866123857343965793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10039327285993905834484229 1882373866123857343965793)
                      ·
                        rfl

theorem cell23_3665910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3665910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665910 prefixEnd_3665910 := by exact prefixLift 3665910
  have htrace : WordTrace (prefixWord ++ tailWord_3665910) baseStart_3665910 baseEnd_3665910 := by
    simpa [prefixWord, tailWord_3665910, baseEnd_3665910] using wordTrace_append hprefix tailTrace_3665910
  have hstable : (prefixWord ++ tailWord_3665910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665910).length < 2 ^ (prefixWord ++ tailWord_3665910).sum := by decide
  have hdescent : baseEnd_3665910 < baseStart_3665910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665913 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 3]
def baseStart_3665913 : Nat := 118140960795 + 3665913 * 2 ^ 59
def prefixEnd_3665913 : Nat := 4983230072969 + 3 ^ 40 * 3665913 * 2
def baseEnd_3665913 : Nat := 1882375406565820832228279

theorem tailTrace_3665913 : CollatzResearch.WordTrace tailWord_3665913 prefixEnd_3665913 1882375406565820832228279 := by
  unfold tailWord_3665913
  simp only [CollatzResearch.WordTrace]
  refine ⟨133706831568030763940090393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89137887712020509293393595 133706831568030763940090393)
  ·
    refine ⟨100280123676023072955067795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133706831568030763940090393 100280123676023072955067795)
    ·
      refine ⟨150420185514034609432601693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100280123676023072955067795 150420185514034609432601693)
      ·
        refine ⟨56407569567762978537225635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150420185514034609432601693 56407569567762978537225635)
        ·
          refine ⟨84611354351644467805838453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56407569567762978537225635 84611354351644467805838453)
          ·
            refine ⟨7932314470466668856797355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84611354351644467805838453 7932314470466668856797355)
            ·
              refine ⟨11898471705700003285196033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932314470466668856797355 11898471705700003285196033)
              ·
                refine ⟨8923853779275002463897025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11898471705700003285196033 8923853779275002463897025)
                ·
                  refine ⟨6692890334456251847922769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8923853779275002463897025 6692890334456251847922769)
                  ·
                    refine ⟨5019667750842188885942077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6692890334456251847922769 5019667750842188885942077)
                    ·
                      refine ⟨1882375406565820832228279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5019667750842188885942077 1882375406565820832228279)
                      ·
                        rfl

theorem cell23_3665913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_3665913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665913 prefixEnd_3665913 := by exact prefixLift 3665913
  have htrace : WordTrace (prefixWord ++ tailWord_3665913) baseStart_3665913 baseEnd_3665913 := by
    simpa [prefixWord, tailWord_3665913, baseEnd_3665913] using wordTrace_append hprefix tailTrace_3665913
  have hstable : (prefixWord ++ tailWord_3665913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665913).length < 2 ^ (prefixWord ++ tailWord_3665913).sum := by decide
  have hdescent : baseEnd_3665913 < baseStart_3665913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665916 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 6]
def baseStart_3665916 : Nat := 118140960795 + 3665916 * 2 ^ 59
def prefixEnd_3665916 : Nat := 4983230072969 + 3 ^ 40 * 3665916 * 2
def baseEnd_3665916 : Nat := 209152994111976035610085

theorem tailTrace_3665916 : CollatzResearch.WordTrace tailWord_3665916 prefixEnd_3665916 209152994111976035610085 := by
  unfold tailWord_3665916
  simp only [CollatzResearch.WordTrace]
  refine ⟨66853470493509947726224801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89137960658013263634966401 66853470493509947726224801)
  ·
    refine ⟨50140102870132460794668601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66853470493509947726224801 50140102870132460794668601)
    ·
      refine ⟨37605077152599345596001451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50140102870132460794668601 37605077152599345596001451)
      ·
        refine ⟨56407615728899018394002177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37605077152599345596001451 56407615728899018394002177)
        ·
          refine ⟨42305711796674263795501633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56407615728899018394002177 42305711796674263795501633)
          ·
            refine ⟨31729283847505697846626225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42305711796674263795501633 31729283847505697846626225)
            ·
              refine ⟨23796962885629273384969669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31729283847505697846626225 23796962885629273384969669)
              ·
                refine ⟨4461930541055488759681813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23796962885629273384969669 4461930541055488759681813)
                ·
                  refine ⟨209152994111976035610085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4461930541055488759681813 209152994111976035610085)
                  ·
                    rfl

theorem cell23_3665916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_3665916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665916 prefixEnd_3665916 := by exact prefixLift 3665916
  have htrace : WordTrace (prefixWord ++ tailWord_3665916) baseStart_3665916 baseEnd_3665916 := by
    simpa [prefixWord, tailWord_3665916, baseEnd_3665916] using wordTrace_append hprefix tailTrace_3665916
  have hstable : (prefixWord ++ tailWord_3665916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665916).length < 2 ^ (prefixWord ++ tailWord_3665916).sum := by decide
  have hdescent : baseEnd_3665916 < baseStart_3665916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665919 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 8]
def baseStart_3665919 : Nat := 118140960795 + 3665919 * 2 ^ 59
def prefixEnd_3665919 : Nat := 4983230072969 + 3 ^ 40 * 3665919 * 2
def baseEnd_3665919 : Nat := 1882378487449747808753251

theorem tailTrace_3665919 : CollatzResearch.WordTrace tailWord_3665919 prefixEnd_3665919 1882378487449747808753251 := by
  unfold tailWord_3665919
  simp only [CollatzResearch.WordTrace]
  refine ⟨133707050406009026964808811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89138033604006017976539207 133707050406009026964808811)
  ·
    refine ⟨200560575609013540447213217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133707050406009026964808811 200560575609013540447213217)
    ·
      refine ⟨150420431706760155335409913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200560575609013540447213217 150420431706760155335409913)
      ·
        refine ⟨112815323780070116501557435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150420431706760155335409913 112815323780070116501557435)
        ·
          refine ⟨169222985670105174752336153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112815323780070116501557435 169222985670105174752336153)
          ·
            refine ⟨126917239252578881064252115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169222985670105174752336153 126917239252578881064252115)
            ·
              refine ⟨190375858878868321596378173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126917239252578881064252115 190375858878868321596378173)
              ·
                refine ⟨71390947079575620598641815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190375858878868321596378173 71390947079575620598641815)
                ·
                  refine ⟨107086420619363430897962723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71390947079575620598641815 107086420619363430897962723)
                  ·
                    refine ⟨160629630929045146346944085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107086420619363430897962723 160629630929045146346944085)
                    ·
                      refine ⟨1882378487449747808753251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 160629630929045146346944085 1882378487449747808753251)
                      ·
                        rfl

theorem cell23_3665919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_3665919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665919 prefixEnd_3665919 := by exact prefixLift 3665919
  have htrace : WordTrace (prefixWord ++ tailWord_3665919) baseStart_3665919 baseEnd_3665919 := by
    simpa [prefixWord, tailWord_3665919, baseEnd_3665919] using wordTrace_append hprefix tailTrace_3665919
  have hstable : (prefixWord ++ tailWord_3665919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665919).length < 2 ^ (prefixWord ++ tailWord_3665919).sum := by decide
  have hdescent : baseEnd_3665919 < baseStart_3665919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665929 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 11]
def baseStart_3665929 : Nat := 118140960795 + 3665929 * 2 ^ 59
def prefixEnd_3665929 : Nat := 4983230072969 + 3 ^ 40 * 3665929 * 2
def baseEnd_3665929 : Nat := 627461207418764256542735

theorem tailTrace_3665929 : CollatzResearch.WordTrace tailWord_3665929 prefixEnd_3665929 627461207418764256542735 := by
  unfold tailWord_3665929
  simp only [CollatzResearch.WordTrace]
  refine ⟨133707415135972798672672841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89138276757315199115115227 133707415135972798672672841)
  ·
    refine ⟨100280561351979599004504631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133707415135972798672672841 100280561351979599004504631)
    ·
      refine ⟨150420842027969398506756947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100280561351979599004504631 150420842027969398506756947)
      ·
        refine ⟨225631263041954097760135421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150420842027969398506756947 225631263041954097760135421)
        ·
          refine ⟨84611723640732786660050783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225631263041954097760135421 84611723640732786660050783)
          ·
            refine ⟨126917585461099179990076175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84611723640732786660050783 126917585461099179990076175)
            ·
              refine ⟨190376378191648769985114263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126917585461099179990076175 190376378191648769985114263)
              ·
                refine ⟨285564567287473154977671395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190376378191648769985114263 285564567287473154977671395)
                ·
                  refine ⟨428346850931209732466507093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285564567287473154977671395 428346850931209732466507093)
                  ·
                    refine ⟨627461207418764256542735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 428346850931209732466507093 627461207418764256542735)
                    ·
                      rfl

theorem cell23_3665929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_3665929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665929 prefixEnd_3665929 := by exact prefixLift 3665929
  have htrace : WordTrace (prefixWord ++ tailWord_3665929) baseStart_3665929 baseEnd_3665929 := by
    simpa [prefixWord, tailWord_3665929, baseEnd_3665929] using wordTrace_append hprefix tailTrace_3665929
  have hstable : (prefixWord ++ tailWord_3665929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665929).length < 2 ^ (prefixWord ++ tailWord_3665929).sum := by decide
  have hdescent : baseEnd_3665929 < baseStart_3665929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665970 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_3665970 : Nat := 118140960795 + 3665970 * 2 ^ 59
def prefixEnd_3665970 : Nat := 4983230072969 + 3 ^ 40 * 3665970 * 2
def baseEnd_3665970 : Nat := 1882404674963127109215517

theorem tailTrace_3665970 : CollatzResearch.WordTrace tailWord_3665970 prefixEnd_3665970 1882404674963127109215517 := by
  unfold tailWord_3665970
  simp only [CollatzResearch.WordTrace]
  refine ⟨33427227632206065668728841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89139273685882841783276909 33427227632206065668728841)
  ·
    refine ⟨25070420724154549251546631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33427227632206065668728841 25070420724154549251546631)
    ·
      refine ⟨37605631086231823877319947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25070420724154549251546631 37605631086231823877319947)
      ·
        refine ⟨56408446629347735815979921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37605631086231823877319947 56408446629347735815979921)
        ·
          refine ⟨42306334972010801861984941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56408446629347735815979921 42306334972010801861984941)
          ·
            refine ⟨15864875614504050698244353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42306334972010801861984941 15864875614504050698244353)
            ·
              refine ⟨11898656710878038023683265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15864875614504050698244353 11898656710878038023683265)
              ·
                refine ⟨8923992533158528517762449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11898656710878038023683265 8923992533158528517762449)
                ·
                  refine ⟨6692994399868896388321837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8923992533158528517762449 6692994399868896388321837)
                  ·
                    refine ⟨2509872899950836145620689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6692994399868896388321837 2509872899950836145620689)
                    ·
                      refine ⟨1882404674963127109215517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509872899950836145620689 1882404674963127109215517)
                      ·
                        rfl

theorem cell23_3665970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_3665970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665970 prefixEnd_3665970 := by exact prefixLift 3665970
  have htrace : WordTrace (prefixWord ++ tailWord_3665970) baseStart_3665970 baseEnd_3665970 := by
    simpa [prefixWord, tailWord_3665970, baseEnd_3665970] using wordTrace_append hprefix tailTrace_3665970
  have hstable : (prefixWord ++ tailWord_3665970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665970).length < 2 ^ (prefixWord ++ tailWord_3665970).sum := by decide
  have hdescent : baseEnd_3665970 < baseStart_3665970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665993 : List Nat := [1, 2, 1, 1, 2, 2, 3, 5, 2, 4]
def baseStart_3665993 : Nat := 118140960795 + 3665993 * 2 ^ 59
def prefixEnd_3665993 : Nat := 4983230072969 + 3 ^ 40 * 3665993 * 2
def baseEnd_3665993 : Nat := 627472161672726839742637

theorem tailTrace_3665993 : CollatzResearch.WordTrace tailWord_3665993 prefixEnd_3665993 627472161672726839742637 := by
  unfold tailWord_3665993
  simp only [CollatzResearch.WordTrace]
  refine ⟨133709749407740937603002633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89139832938493958402001755 133709749407740937603002633)
  ·
    refine ⟨100282312055805703202251975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133709749407740937603002633 100282312055805703202251975)
    ·
      refine ⟨150423468083708554803377963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100282312055805703202251975 150423468083708554803377963)
      ·
        refine ⟨225635202125562832205066945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150423468083708554803377963 225635202125562832205066945)
        ·
          refine ⟨169226401594172124153800209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225635202125562832205066945 169226401594172124153800209)
          ·
            refine ⟨126919801195629093115350157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169226401594172124153800209 126919801195629093115350157)
            ·
              refine ⟨47594925448360909918256309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126919801195629093115350157 47594925448360909918256309)
              ·
                refine ⟨4462024260783835304836529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47594925448360909918256309 4462024260783835304836529)
                ·
                  refine ⟨3346518195587876478627397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462024260783835304836529 3346518195587876478627397)
                  ·
                    refine ⟨627472161672726839742637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3346518195587876478627397 627472161672726839742637)
                    ·
                      rfl

theorem cell23_3665993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 4].length) (baseStart_3665993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665993 prefixEnd_3665993 := by exact prefixLift 3665993
  have htrace : WordTrace (prefixWord ++ tailWord_3665993) baseStart_3665993 baseEnd_3665993 := by
    simpa [prefixWord, tailWord_3665993, baseEnd_3665993] using wordTrace_append hprefix tailTrace_3665993
  have hstable : (prefixWord ++ tailWord_3665993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665993).length < 2 ^ (prefixWord ++ tailWord_3665993).sum := by decide
  have hdescent : baseEnd_3665993 < baseStart_3665993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665996 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3665996 : Nat := 118140960795 + 3665996 * 2 ^ 59
def prefixEnd_3665996 : Nat := 4983230072969 + 3 ^ 40 * 3665996 * 2
def baseEnd_3665996 : Nat := 1882418025460144007490397

theorem tailTrace_3665996 : CollatzResearch.WordTrace tailWord_3665996 prefixEnd_3665996 1882418025460144007490397 := by
  unfold tailWord_3665996
  simp only [CollatzResearch.WordTrace]
  refine ⟨66854929413365034557680921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89139905884486712743574561 66854929413365034557680921)
  ·
    refine ⟨50141197060023775918260691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66854929413365034557680921 50141197060023775918260691)
    ·
      refine ⟨75211795590035663877391037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50141197060023775918260691 75211795590035663877391037)
      ·
        refine ⟨28204423346263373954021639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75211795590035663877391037 28204423346263373954021639)
        ·
          refine ⟨42306635019395060931032459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28204423346263373954021639 42306635019395060931032459)
          ·
            refine ⟨63459952529092591396548689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42306635019395060931032459 63459952529092591396548689)
            ·
              refine ⟨47594964396819443547411517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63459952529092591396548689 47594964396819443547411517)
              ·
                refine ⟨17848111648807291330279319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47594964396819443547411517 17848111648807291330279319)
                ·
                  refine ⟨26772167473210936995418979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17848111648807291330279319 26772167473210936995418979)
                  ·
                    refine ⟨40158251209816405493128469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26772167473210936995418979 40158251209816405493128469)
                    ·
                      refine ⟨1882418025460144007490397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40158251209816405493128469 1882418025460144007490397)
                      ·
                        rfl

theorem cell23_3665996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3665996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3665996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3665996 prefixEnd_3665996 := by exact prefixLift 3665996
  have htrace : WordTrace (prefixWord ++ tailWord_3665996) baseStart_3665996 baseEnd_3665996 := by
    simpa [prefixWord, tailWord_3665996, baseEnd_3665996] using wordTrace_append hprefix tailTrace_3665996
  have hstable : (prefixWord ++ tailWord_3665996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665996).length < 2 ^ (prefixWord ++ tailWord_3665996).sum := by decide
  have hdescent : baseEnd_3665996 < baseStart_3665996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666014 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3666014 : Nat := 118140960795 + 3666014 * 2 ^ 59
def prefixEnd_3666014 : Nat := 4983230072969 + 3 ^ 40 * 3666014 * 2
def baseEnd_3666014 : Nat := 627475756037308312355105

theorem tailTrace_3666014 : CollatzResearch.WordTrace tailWord_3666014 prefixEnd_3666014 627475756037308312355105 := by
  unfold tailWord_3666014
  simp only [CollatzResearch.WordTrace]
  refine ⟨16713814417583107273689637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89140343560443238793011397 16713814417583107273689637)
  ·
    refine ⟨3133840203296832613816807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16713814417583107273689637 3133840203296832613816807)
    ·
      refine ⟨4700760304945248920725211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3133840203296832613816807 4700760304945248920725211)
      ·
        refine ⟨7051140457417873381087817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4700760304945248920725211 7051140457417873381087817)
        ·
          refine ⟨5288355343063405035815863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7051140457417873381087817 5288355343063405035815863)
          ·
            refine ⟨7932533014595107553723795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288355343063405035815863 7932533014595107553723795)
            ·
              refine ⟨11898799521892661330585693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932533014595107553723795 11898799521892661330585693)
              ·
                refine ⟨4462049820709747998969635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11898799521892661330585693 4462049820709747998969635)
                ·
                  refine ⟨6693074731064621998454453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462049820709747998969635 6693074731064621998454453)
                  ·
                    refine ⟨627475756037308312355105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6693074731064621998454453 627475756037308312355105)
                    ·
                      rfl

theorem cell23_3666014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3666014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666014 prefixEnd_3666014 := by exact prefixLift 3666014
  have htrace : WordTrace (prefixWord ++ tailWord_3666014) baseStart_3666014 baseEnd_3666014 := by
    simpa [prefixWord, tailWord_3666014, baseEnd_3666014] using wordTrace_append hprefix tailTrace_3666014
  have hstable : (prefixWord ++ tailWord_3666014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666014).length < 2 ^ (prefixWord ++ tailWord_3666014).sum := by decide
  have hdescent : baseEnd_3666014 < baseStart_3666014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666034 : List Nat := [3, 2, 1, 2, 2, 2, 2, 4, 1, 2, 2]
def baseStart_3666034 : Nat := 118140960795 + 3666034 * 2 ^ 59
def prefixEnd_3666034 : Nat := 4983230072969 + 3 ^ 40 * 3666034 * 2
def baseEnd_3666034 : Nat := 1882437537725014858815223

theorem tailTrace_3666034 : CollatzResearch.WordTrace tailWord_3666034 prefixEnd_3666034 1882437537725014858815223 := by
  unfold tailWord_3666034
  simp only [CollatzResearch.WordTrace]
  refine ⟨33427811200148100401311289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89140829867061601070163437 33427811200148100401311289)
  ·
    refine ⟨25070858400111075300983467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33427811200148100401311289 25070858400111075300983467)
    ·
      refine ⟨37606287600166612951475201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25070858400111075300983467 37606287600166612951475201)
      ·
        refine ⟨28204715700124959713606401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37606287600166612951475201 28204715700124959713606401)
        ·
          refine ⟨21153536775093719785204801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28204715700124959713606401 21153536775093719785204801)
          ·
            refine ⟨15865152581320289838903601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21153536775093719785204801 15865152581320289838903601)
            ·
              refine ⟨11898864435990217379177701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15865152581320289838903601 11898864435990217379177701)
              ·
                refine ⟨2231037081748165758595819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11898864435990217379177701 2231037081748165758595819)
                ·
                  refine ⟨3346555622622248637893729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231037081748165758595819 3346555622622248637893729)
                  ·
                    refine ⟨2509916716966686478420297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3346555622622248637893729 2509916716966686478420297)
                    ·
                      refine ⟨1882437537725014858815223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509916716966686478420297 1882437537725014858815223)
                      ·
                        rfl

theorem cell23_3666034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_3666034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666034 prefixEnd_3666034 := by exact prefixLift 3666034
  have htrace : WordTrace (prefixWord ++ tailWord_3666034) baseStart_3666034 baseEnd_3666034 := by
    simpa [prefixWord, tailWord_3666034, baseEnd_3666034] using wordTrace_append hprefix tailTrace_3666034
  have hstable : (prefixWord ++ tailWord_3666034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666034).length < 2 ^ (prefixWord ++ tailWord_3666034).sum := by decide
  have hdescent : baseEnd_3666034 < baseStart_3666034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666077 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_3666077 : Nat := 118140960795 + 3666077 * 2 ^ 59
def prefixEnd_3666077 : Nat := 4983230072969 + 3 ^ 40 * 3666077 * 2
def baseEnd_3666077 : Nat := 1882459617393158190577525

theorem tailTrace_3666077 : CollatzResearch.WordTrace tailWord_3666077 prefixEnd_3666077 1882459617393158190577525 := by
  unfold tailWord_3666077
  simp only [CollatzResearch.WordTrace]
  refine ⟨133712813139436619949060485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89141875426291079966040323 133712813139436619949060485)
  ·
    refine ⟨25071152463644366240448841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133712813139436619949060485 25071152463644366240448841)
    ·
      refine ⟨18803364347733274680336631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25071152463644366240448841 18803364347733274680336631)
      ·
        refine ⟨28205046521599912020504947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18803364347733274680336631 28205046521599912020504947)
        ·
          refine ⟨42307569782399868030757421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28205046521599912020504947 42307569782399868030757421)
          ·
            refine ⟨15865338668399950511534033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42307569782399868030757421 15865338668399950511534033)
            ·
              refine ⟨11899004001299962883650525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15865338668399950511534033 11899004001299962883650525)
              ·
                refine ⟨4462126500487486081368947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11899004001299962883650525 4462126500487486081368947)
                ·
                  refine ⟨6693189750731229122053421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462126500487486081368947 6693189750731229122053421)
                  ·
                    refine ⟨2509946156524210920770033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6693189750731229122053421 2509946156524210920770033)
                    ·
                      refine ⟨1882459617393158190577525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509946156524210920770033 1882459617393158190577525)
                      ·
                        rfl

theorem cell23_3666077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_3666077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666077 prefixEnd_3666077 := by exact prefixLift 3666077
  have htrace : WordTrace (prefixWord ++ tailWord_3666077) baseStart_3666077 baseEnd_3666077 := by
    simpa [prefixWord, tailWord_3666077, baseEnd_3666077] using wordTrace_append hprefix tailTrace_3666077
  have hstable : (prefixWord ++ tailWord_3666077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666077).length < 2 ^ (prefixWord ++ tailWord_3666077).sum := by decide
  have hdescent : baseEnd_3666077 < baseStart_3666077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666107 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 2, 2, 2]
def baseStart_3666107 : Nat := 118140960795 + 3666107 * 2 ^ 59
def prefixEnd_3666107 : Nat := 4983230072969 + 3 ^ 40 * 3666107 * 2
def baseEnd_3666107 : Nat := 1882475021812793073202387

theorem tailTrace_3666107 : CollatzResearch.WordTrace tailWord_3666107 prefixEnd_3666107 1882475021812793073202387 := by
  unfold tailWord_3666107
  simp only [CollatzResearch.WordTrace]
  refine ⟨133713907329327935072652575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89142604886218623381768383 133713907329327935072652575)
  ·
    refine ⟨200570860993991902608978863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133713907329327935072652575 200570860993991902608978863)
    ·
      refine ⟨300856291490987853913468295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200570860993991902608978863 300856291490987853913468295)
      ·
        refine ⟨451284437236481780870202443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300856291490987853913468295 451284437236481780870202443)
        ·
          refine ⟨676926655854722671305303665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451284437236481780870202443 676926655854722671305303665)
          ·
            refine ⟨507694991891042003478977749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676926655854722671305303665 507694991891042003478977749)
            ·
              refine ⟨11899101372446296956538541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 507694991891042003478977749 11899101372446296956538541)
              ·
                refine ⟨4462163014667361358701953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11899101372446296956538541 4462163014667361358701953)
                ·
                  refine ⟨3346622261000521019026465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462163014667361358701953 3346622261000521019026465)
                  ·
                    refine ⟨2509966695750390764269849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3346622261000521019026465 2509966695750390764269849)
                    ·
                      refine ⟨1882475021812793073202387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509966695750390764269849 1882475021812793073202387)
                      ·
                        rfl

theorem cell23_3666107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 2, 2].length) (baseStart_3666107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666107 prefixEnd_3666107 := by exact prefixLift 3666107
  have htrace : WordTrace (prefixWord ++ tailWord_3666107) baseStart_3666107 baseEnd_3666107 := by
    simpa [prefixWord, tailWord_3666107, baseEnd_3666107] using wordTrace_append hprefix tailTrace_3666107
  have hstable : (prefixWord ++ tailWord_3666107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666107).length < 2 ^ (prefixWord ++ tailWord_3666107).sum := by decide
  have hdescent : baseEnd_3666107 < baseStart_3666107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666124 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3666124 : Nat := 118140960795 + 3666124 * 2 ^ 59
def prefixEnd_3666124 : Nat := 4983230072969 + 3 ^ 40 * 3666124 * 2
def baseEnd_3666124 : Nat := 1882483750983919506689809

theorem tailTrace_3666124 : CollatzResearch.WordTrace tailWord_3666124 prefixEnd_3666124 1882483750983919506689809 := by
  unfold tailWord_3666124
  simp only [CollatzResearch.WordTrace]
  refine ⟨66857263685133173488010713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89143018246844231317347617 66857263685133173488010713)
  ·
    refine ⟨50142947763849880116008035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66857263685133173488010713 50142947763849880116008035)
    ·
      refine ⟨75214421645774820174012053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50142947763849880116008035 75214421645774820174012053)
      ·
        refine ⟨3525676014645694695656815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75214421645774820174012053 3525676014645694695656815)
        ·
          refine ⟨5288514021968542043485223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525676014645694695656815 5288514021968542043485223)
          ·
            refine ⟨7932771032952813065227835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288514021968542043485223 7932771032952813065227835)
            ·
              refine ⟨11899156549429219597841753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932771032952813065227835 11899156549429219597841753)
              ·
                refine ⟨8924367412071914698381315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11899156549429219597841753 8924367412071914698381315)
                ·
                  refine ⟨13386551118107872047571973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8924367412071914698381315 13386551118107872047571973)
                  ·
                    refine ⟨2509978334645226008919745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13386551118107872047571973 2509978334645226008919745)
                    ·
                      refine ⟨1882483750983919506689809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509978334645226008919745 1882483750983919506689809)
                      ·
                        rfl

theorem cell23_3666124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3666124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666124 prefixEnd_3666124 := by exact prefixLift 3666124
  have htrace : WordTrace (prefixWord ++ tailWord_3666124) baseStart_3666124 baseEnd_3666124 := by
    simpa [prefixWord, tailWord_3666124, baseEnd_3666124] using wordTrace_append hprefix tailTrace_3666124
  have hstable : (prefixWord ++ tailWord_3666124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666124).length < 2 ^ (prefixWord ++ tailWord_3666124).sum := by decide
  have hdescent : baseEnd_3666124 < baseStart_3666124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666141 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3666141 : Nat := 118140960795 + 3666141 * 2 ^ 59
def prefixEnd_3666141 : Nat := 4983230072969 + 3 ^ 40 * 3666141 * 2
def baseEnd_3666141 : Nat := 1882492480155045940177231

theorem tailTrace_3666141 : CollatzResearch.WordTrace tailWord_3666141 prefixEnd_3666141 1882492480155045940177231 := by
  unfold tailWord_3666141
  simp only [CollatzResearch.WordTrace]
  refine ⟨133715147411204758879390277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89143431607469839252926851 133715147411204758879390277)
  ·
    refine ⟨25071590139600892289885677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133715147411204758879390277 25071590139600892289885677)
    ·
      refine ⟨9401846302350334608707129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25071590139600892289885677 9401846302350334608707129)
      ·
        refine ⟨7051384726762750956530347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9401846302350334608707129 7051384726762750956530347)
        ·
          refine ⟨10577077090144126434795521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051384726762750956530347 10577077090144126434795521)
          ·
            refine ⟨7932807817608094826096641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10577077090144126434795521 7932807817608094826096641)
            ·
              refine ⟨5949605863206071119572481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7932807817608094826096641 5949605863206071119572481)
              ·
                refine ⟨4462204397404553339679361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949605863206071119572481 4462204397404553339679361)
                ·
                  refine ⟨3346653298053415004759521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462204397404553339679361 3346653298053415004759521)
                  ·
                    refine ⟨2509989973540061253569641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3346653298053415004759521 2509989973540061253569641)
                    ·
                      refine ⟨1882492480155045940177231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2509989973540061253569641 1882492480155045940177231)
                      ·
                        rfl

theorem cell23_3666141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3666141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666141 prefixEnd_3666141 := by exact prefixLift 3666141
  have htrace : WordTrace (prefixWord ++ tailWord_3666141) baseStart_3666141 baseEnd_3666141 := by
    simpa [prefixWord, tailWord_3666141, baseEnd_3666141] using wordTrace_append hprefix tailTrace_3666141
  have hstable : (prefixWord ++ tailWord_3666141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666141).length < 2 ^ (prefixWord ++ tailWord_3666141).sum := by decide
  have hdescent : baseEnd_3666141 < baseStart_3666141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666157 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3666157 : Nat := 118140960795 + 3666157 * 2 ^ 59
def prefixEnd_3666157 : Nat := 4983230072969 + 3 ^ 40 * 3666157 * 2
def baseEnd_3666157 : Nat := 1882500695845517877577157

theorem tailTrace_3666157 : CollatzResearch.WordTrace tailWord_3666157 prefixEnd_3666157 1882500695845517877577157 := by
  unfold tailWord_3666157
  simp only [CollatzResearch.WordTrace]
  refine ⟨133715730979146793611972725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89143820652764529074648483 133715730979146793611972725)
  ·
    refine ⟨12535849779295011901122443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133715730979146793611972725 12535849779295011901122443)
    ·
      refine ⟨18803774668942517851683665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12535849779295011901122443 18803774668942517851683665)
      ·
        refine ⟨14102831001706888388762749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18803774668942517851683665 14102831001706888388762749)
        ·
          refine ⟨5288561625640083145786031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14102831001706888388762749 5288561625640083145786031)
          ·
            refine ⟨7932842438460124718679047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288561625640083145786031 7932842438460124718679047)
            ·
              refine ⟨11899263657690187078018571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932842438460124718679047 11899263657690187078018571)
              ·
                refine ⟨17848895486535280617027857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11899263657690187078018571 17848895486535280617027857)
                ·
                  refine ⟨13386671614901460462770893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17848895486535280617027857 13386671614901460462770893)
                  ·
                    refine ⟨5020001855588047673539085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13386671614901460462770893 5020001855588047673539085)
                    ·
                      refine ⟨1882500695845517877577157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5020001855588047673539085 1882500695845517877577157)
                      ·
                        rfl

theorem cell23_3666157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3666157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666157 prefixEnd_3666157 := by exact prefixLift 3666157
  have htrace : WordTrace (prefixWord ++ tailWord_3666157) baseStart_3666157 baseEnd_3666157 := by
    simpa [prefixWord, tailWord_3666157, baseEnd_3666157] using wordTrace_append hprefix tailTrace_3666157
  have hstable : (prefixWord ++ tailWord_3666157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666157).length < 2 ^ (prefixWord ++ tailWord_3666157).sum := by decide
  have hdescent : baseEnd_3666157 < baseStart_3666157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666163 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 4]
def baseStart_3666163 : Nat := 118140960795 + 3666163 * 2 ^ 59
def prefixEnd_3666163 : Nat := 4983230072969 + 3 ^ 40 * 3666163 * 2
def baseEnd_3666163 : Nat := 1882503776729444854102129

theorem tailTrace_3666163 : CollatzResearch.WordTrace tailWord_3666163 prefixEnd_3666163 1882503776729444854102129 := by
  unfold tailWord_3666163
  simp only [CollatzResearch.WordTrace]
  refine ⟨133715949817125056636691143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89143966544750037757794095 133715949817125056636691143)
  ·
    refine ⟨200573924725687584955036715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133715949817125056636691143 200573924725687584955036715)
    ·
      refine ⟨300860887088531377432555073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200573924725687584955036715 300860887088531377432555073)
      ·
        refine ⟨225645665316398533074416305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300860887088531377432555073 225645665316398533074416305)
        ·
          refine ⟨169234248987298899805812229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225645665316398533074416305 169234248987298899805812229)
          ·
            refine ⟨31731421685118543713589793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169234248987298899805812229 31731421685118543713589793)
            ·
              refine ⟨23798566263838907785192345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31731421685118543713589793 23798566263838907785192345)
              ·
                refine ⟨17848924697879180838894259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23798566263838907785192345 17848924697879180838894259)
                ·
                  refine ⟨26773387046818771258341389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17848924697879180838894259 26773387046818771258341389)
                  ·
                    refine ⟨10040020142557039221878021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26773387046818771258341389 10040020142557039221878021)
                    ·
                      refine ⟨1882503776729444854102129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10040020142557039221878021 1882503776729444854102129)
                      ·
                        rfl

theorem cell23_3666163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_3666163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666163 prefixEnd_3666163 := by exact prefixLift 3666163
  have htrace : WordTrace (prefixWord ++ tailWord_3666163) baseStart_3666163 baseEnd_3666163 := by
    simpa [prefixWord, tailWord_3666163, baseEnd_3666163] using wordTrace_append hprefix tailTrace_3666163
  have hstable : (prefixWord ++ tailWord_3666163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666163).length < 2 ^ (prefixWord ++ tailWord_3666163).sum := by decide
  have hdescent : baseEnd_3666163 < baseStart_3666163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666190 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_3666190 : Nat := 118140960795 + 3666190 * 2 ^ 59
def prefixEnd_3666190 : Nat := 4983230072969 + 3 ^ 40 * 3666190 * 2
def baseEnd_3666190 : Nat := 627505880235705416154835

theorem tailTrace_3666190 : CollatzResearch.WordTrace tailWord_3666190 prefixEnd_3666190 627505880235705416154835 := by
  unfold tailWord_3666190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16714616823503405030990503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89144623058684826831949349 16714616823503405030990503)
  ·
    refine ⟨25071925235255107546485755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16714616823503405030990503 25071925235255107546485755)
    ·
      refine ⟨37607887852882661319728633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25071925235255107546485755 37607887852882661319728633)
      ·
        refine ⟨28205915889661995989796475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37607887852882661319728633 28205915889661995989796475)
        ·
          refine ⟨42308873834492993984694713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28205915889661995989796475 42308873834492993984694713)
          ·
            refine ⟨31731655375869745488521035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42308873834492993984694713 31731655375869745488521035)
            ·
              refine ⟨47597483063804618232781553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31731655375869745488521035 47597483063804618232781553)
              ·
                refine ⟨35698112297853463674586165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47597483063804618232781553 35698112297853463674586165)
                ·
                  refine ⟨3346698027923762219492453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35698112297853463674586165 3346698027923762219492453)
                  ·
                    refine ⟨627505880235705416154835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3346698027923762219492453 627505880235705416154835)
                    ·
                      rfl

theorem cell23_3666190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_3666190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666190 prefixEnd_3666190 := by exact prefixLift 3666190
  have htrace : WordTrace (prefixWord ++ tailWord_3666190) baseStart_3666190 baseEnd_3666190 := by
    simpa [prefixWord, tailWord_3666190, baseEnd_3666190] using wordTrace_append hprefix tailTrace_3666190
  have hstable : (prefixWord ++ tailWord_3666190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666190).length < 2 ^ (prefixWord ++ tailWord_3666190).sum := by decide
  have hdescent : baseEnd_3666190 < baseStart_3666190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666193 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_3666193 : Nat := 118140960795 + 3666193 * 2 ^ 59
def prefixEnd_3666193 : Nat := 4983230072969 + 3 ^ 40 * 3666193 * 2
def baseEnd_3666193 : Nat := 1882519181149079736726991

theorem tailTrace_3666193 : CollatzResearch.WordTrace tailWord_3666193 prefixEnd_3666193 1882519181149079736726991 := by
  unfold tailWord_3666193
  simp only [CollatzResearch.WordTrace]
  refine ⟨133717044007016371760283233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89144696004677581173522155 133717044007016371760283233)
  ·
    refine ⟨100287783005262278820212425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133717044007016371760283233 100287783005262278820212425)
    ·
      refine ⟨75215837253946709115159319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100287783005262278820212425 75215837253946709115159319)
      ·
        refine ⟨112823755880920063672738979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75215837253946709115159319 112823755880920063672738979)
        ·
          refine ⟨169235633821380095509108469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112823755880920063672738979 169235633821380095509108469)
          ·
            refine ⟨15865840670754383953978919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169235633821380095509108469 15865840670754383953978919)
            ·
              refine ⟨23798761006131575930968379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15865840670754383953978919 23798761006131575930968379)
              ·
                refine ⟨35698141509197363896452569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23798761006131575930968379 35698141509197363896452569)
                ·
                  refine ⟨26773606131898022922339427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35698141509197363896452569 26773606131898022922339427)
                  ·
                    refine ⟨40160409197847034383509141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26773606131898022922339427 40160409197847034383509141)
                    ·
                      refine ⟨1882519181149079736726991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40160409197847034383509141 1882519181149079736726991)
                      ·
                        rfl

theorem cell23_3666193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_3666193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666193 prefixEnd_3666193 := by exact prefixLift 3666193
  have htrace : WordTrace (prefixWord ++ tailWord_3666193) baseStart_3666193 baseEnd_3666193 := by
    simpa [prefixWord, tailWord_3666193, baseEnd_3666193] using wordTrace_append hprefix tailTrace_3666193
  have hstable : (prefixWord ++ tailWord_3666193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666193).length < 2 ^ (prefixWord ++ tailWord_3666193).sum := by decide
  have hdescent : baseEnd_3666193 < baseStart_3666193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666200 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_3666200 : Nat := 118140960795 + 3666200 * 2 ^ 59
def prefixEnd_3666200 : Nat := 4983230072969 + 3 ^ 40 * 3666200 * 2
def baseEnd_3666200 : Nat := 1882522775513661209339459

theorem tailTrace_3666200 : CollatzResearch.WordTrace tailWord_3666200 prefixEnd_3666200 1882522775513661209339459 := by
  unfold tailWord_3666200
  simp only [CollatzResearch.WordTrace]
  refine ⟨66858649658995505977894027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89144866211994007970525369 66858649658995505977894027)
  ·
    refine ⟨100287974488493258966841041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66858649658995505977894027 100287974488493258966841041)
    ·
      refine ⟨75215980866369944225130781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100287974488493258966841041 75215980866369944225130781)
      ·
        refine ⟨28205992824888729084424043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75215980866369944225130781 28205992824888729084424043)
        ·
          refine ⟨42308989237333093626636065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28205992824888729084424043 42308989237333093626636065)
          ·
            refine ⟨31731741927999820219977049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42308989237333093626636065 31731741927999820219977049)
            ·
              refine ⟨23798806445999865164982787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31731741927999820219977049 23798806445999865164982787)
              ·
                refine ⟨35698209668999797747474181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23798806445999865164982787 35698209668999797747474181)
                ·
                  refine ⟨6693414312937462077651409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35698209668999797747474181 6693414312937462077651409)
                  ·
                    refine ⟨5020060734703096558238557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6693414312937462077651409 5020060734703096558238557)
                    ·
                      refine ⟨1882522775513661209339459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5020060734703096558238557 1882522775513661209339459)
                      ·
                        rfl

theorem cell23_3666200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_3666200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666200 prefixEnd_3666200 := by exact prefixLift 3666200
  have htrace : WordTrace (prefixWord ++ tailWord_3666200) baseStart_3666200 baseEnd_3666200 := by
    simpa [prefixWord, tailWord_3666200, baseEnd_3666200] using wordTrace_append hprefix tailTrace_3666200
  have hstable : (prefixWord ++ tailWord_3666200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666200).length < 2 ^ (prefixWord ++ tailWord_3666200).sum := by decide
  have hdescent : baseEnd_3666200 < baseStart_3666200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666207 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 3, 4]
def baseStart_3666207 : Nat := 118140960795 + 3666207 * 2 ^ 59
def prefixEnd_3666207 : Nat := 4983230072969 + 3 ^ 40 * 3666207 * 2
def baseEnd_3666207 : Nat := 627508789959414227317309

theorem tailTrace_3666207 : CollatzResearch.WordTrace tailWord_3666207 prefixEnd_3666207 627508789959414227317309 := by
  unfold tailWord_3666207
  simp only [CollatzResearch.WordTrace]
  refine ⟨133717554628965652151292875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89145036419310434767528583 133717554628965652151292875)
  ·
    refine ⟨200576331943448478226939313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133717554628965652151292875 200576331943448478226939313)
    ·
      refine ⟨150432248957586358670204485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200576331943448478226939313 150432248957586358670204485)
      ·
        refine ⟨28206046679547442250663341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150432248957586358670204485 28206046679547442250663341)
        ·
          refine ⟨10577267504830290843998753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28206046679547442250663341 10577267504830290843998753)
          ·
            refine ⟨7932950628622718132999065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10577267504830290843998753 7932950628622718132999065)
            ·
              refine ⟨5949712971467038599749299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7932950628622718132999065 5949712971467038599749299)
              ·
                refine ⟨8924569457200557899623949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5949712971467038599749299 8924569457200557899623949)
                ·
                  refine ⟨3346713546450209212358981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8924569457200557899623949 3346713546450209212358981)
                  ·
                    refine ⟨627508789959414227317309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3346713546450209212358981 627508789959414227317309)
                    ·
                      rfl

theorem cell23_3666207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 4].length) (baseStart_3666207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666207 prefixEnd_3666207 := by exact prefixLift 3666207
  have htrace : WordTrace (prefixWord ++ tailWord_3666207) baseStart_3666207 baseEnd_3666207 := by
    simpa [prefixWord, tailWord_3666207, baseEnd_3666207] using wordTrace_append hprefix tailTrace_3666207
  have hstable : (prefixWord ++ tailWord_3666207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666207).length < 2 ^ (prefixWord ++ tailWord_3666207).sum := by decide
  have hdescent : baseEnd_3666207 < baseStart_3666207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666257 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 4, 3, 2]
def baseStart_3666257 : Nat := 118140960795 + 3666257 * 2 ^ 59
def prefixEnd_3666257 : Nat := 4983230072969 + 3 ^ 40 * 3666257 * 2
def baseEnd_3666257 : Nat := 1882552043910967486326697

theorem tailTrace_3666257 : CollatzResearch.WordTrace tailWord_3666257 prefixEnd_3666257 1882552043910967486326697 := by
  unfold tailWord_3666257
  simp only [CollatzResearch.WordTrace]
  refine ⟨133719378278784510690613025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89146252185856340460408683 133719378278784510690613025)
  ·
    refine ⟨100289533709088383017959769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133719378278784510690613025 100289533709088383017959769)
    ·
      refine ⟨75217150281816287263469827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100289533709088383017959769 75217150281816287263469827)
      ·
        refine ⟨112825725422724430895204741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75217150281816287263469827 112825725422724430895204741)
        ·
          refine ⟨21154823516760830792850889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112825725422724430895204741 21154823516760830792850889)
          ·
            refine ⟨15866117637570623094638167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21154823516760830792850889 15866117637570623094638167)
            ·
              refine ⟨23799176456355934641957251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15866117637570623094638167 23799176456355934641957251)
              ·
                refine ⟨35698764684533901962935877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23799176456355934641957251 35698764684533901962935877)
                ·
                  refine ⟨6693518378350106618050477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35698764684533901962935877 6693518378350106618050477)
                  ·
                    refine ⟨2510069391881289981768929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6693518378350106618050477 2510069391881289981768929)
                    ·
                      refine ⟨1882552043910967486326697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2510069391881289981768929 1882552043910967486326697)
                      ·
                        rfl

theorem cell23_3666257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_3666257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3666257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3666257 prefixEnd_3666257 := by exact prefixLift 3666257
  have htrace : WordTrace (prefixWord ++ tailWord_3666257) baseStart_3666257 baseEnd_3666257 := by
    simpa [prefixWord, tailWord_3666257, baseEnd_3666257] using wordTrace_append hprefix tailTrace_3666257
  have hstable : (prefixWord ++ tailWord_3666257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666257).length < 2 ^ (prefixWord ++ tailWord_3666257).sum := by decide
  have hdescent : baseEnd_3666257 < baseStart_3666257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
